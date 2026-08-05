use std::error::Error;

use covalence_repl::{
    EndpointDescription, ExpectedKernelIdentity, KernelId, NativeKernelProcess, Repl,
    ServiceIdentity, ServiceOperation, ServiceResult, SessionInitiator, SignedHolArtifact,
    SignedServiceSession,
};

type Result<T> = std::result::Result<T, Box<dyn Error>>;

fn binary() -> Option<&'static str> {
    // Cargo provides the sibling executable for genuine process tests. Buck
    // compiles integration targets independently; its unit target still runs
    // the framing and signed-transcript codec tests in covalence-repl.
    option_env!("CARGO_BIN_EXE_nucleus")
}

struct ConnectedKernel {
    process: NativeKernelProcess,
    session: SignedServiceSession,
    expected: ExpectedKernelIdentity,
    description: EndpointDescription,
}

impl ConnectedKernel {
    fn spawn(binary: &str, kernel_id: u32) -> Result<Self> {
        let mut process = NativeKernelProcess::spawn(binary)?;
        let description = process.describe()?;
        let identity = description.identity();
        let expected = ExpectedKernelIdentity::from_untrusted_parts(
            KernelId::from_u32(kernel_id),
            &identity.signer().to_string(),
            &identity.public_key(),
        )?;
        let initiator = SessionInitiator::begin(
            ServiceIdentity::new(identity.signer(), identity.public_key())?,
            &description,
        )?;
        let accepted = process.open_session(initiator.request())?;
        let session = initiator.accept(&accepted)?;
        Ok(Self {
            process,
            session,
            expected,
            description,
        })
    }

    fn command(&mut self, operation: ServiceOperation) -> Result<ServiceResult> {
        let command = self.session.command(operation)?;
        let reply = self.process.execute(&command)?;
        Ok(self.session.accept_reply(&command, reply)?)
    }

    fn open_hol(&mut self) -> Result<u64> {
        match self.command(ServiceOperation::OpenHol)? {
            ServiceResult::Opened(connection) => Ok(connection),
            _ => Err("native kernel did not open HOL".into()),
        }
    }

    fn produce(&mut self, connection: u64) -> Result<SignedHolArtifact> {
        match self.command(ServiceOperation::ProduceSignedHol(connection))? {
            ServiceResult::Produced(produced) => Ok(produced.into_artifact()),
            _ => Err("native kernel did not produce artifact".into()),
        }
    }

    fn shutdown(mut self) -> Result<()> {
        assert!(matches!(
            self.command(ServiceOperation::Shutdown)?,
            ServiceResult::Goodbye
        ));
        assert!(self.process.wait_for_exit()?.success());
        Ok(())
    }
}

#[test]
fn process_boundary_rejects_tamper_and_attacker_then_exits() -> Result<()> {
    let Some(binary) = binary() else {
        return Ok(());
    };
    let mut honest = ConnectedKernel::spawn(binary, 1)?;
    let mut attacker = ConnectedKernel::spawn(binary, 2)?;
    assert_ne!(honest.expected.signer(), attacker.expected.signer());
    let attacker_identity =
        ServiceIdentity::new(attacker.expected.signer(), *attacker.expected.public_key())?;
    assert!(SessionInitiator::begin(attacker_identity, &honest.description).is_err());

    let source = honest.open_hol()?;
    let target = honest.open_hol()?;
    let honest_artifact = honest.produce(source)?;
    let attacker_source = attacker.open_hol()?;
    let attack = attacker.produce(attacker_source)?;

    let result = honest.command(ServiceOperation::ReceiveSignedHol {
        connection: target,
        expected: honest.expected.clone(),
        artifact: Box::new(attack),
    })?;
    assert!(matches!(
        result,
        ServiceResult::OperationError(message) if message.contains("signer-pinned")
    ));

    let mut tampered_image = honest_artifact.image().to_vec();
    let last = tampered_image.last_mut().ok_or("empty HOL image")?;
    *last ^= 1;
    let tampered = SignedHolArtifact::from_untrusted_parts(
        honest_artifact.namespace_id(),
        tampered_image,
        &honest_artifact.schema().to_string(),
        &honest_artifact.image_hash().to_string(),
        &honest_artifact.signer().to_string(),
        honest_artifact.public_key().to_vec(),
        honest_artifact.signature().to_vec(),
    )?;
    let result = honest.command(ServiceOperation::ReceiveSignedHol {
        connection: target,
        expected: honest.expected.clone(),
        artifact: Box::new(tampered),
    })?;
    assert!(matches!(
        result,
        ServiceResult::OperationError(message) if message.contains("signature-authenticated")
    ));

    let result = honest.command(ServiceOperation::ReceiveSignedHol {
        connection: target,
        expected: honest.expected.clone(),
        artifact: Box::new(honest_artifact),
    })?;
    let ServiceResult::Received(received) = result else {
        return Err("honest artifact was not received".into());
    };
    assert_eq!(received.import_id(), 0);
    assert_eq!(received.context_id(), 0);
    assert_eq!(received.conclusion_id(), 8);

    assert!(matches!(
        honest.command(ServiceOperation::CloseHol(source))?,
        ServiceResult::Closed
    ));
    assert!(matches!(
        honest.command(ServiceOperation::ProduceSignedHol(source))?,
        ServiceResult::OperationError(message) if message.contains("unknown HOL connection")
    ));
    attacker.shutdown()?;
    honest.shutdown()?;
    Ok(())
}

#[test]
fn terminal_command_drives_the_signed_native_endpoint() -> Result<()> {
    let Some(binary) = binary() else {
        return Ok(());
    };
    let output = std::process::Command::new(binary)
        .args(["--native-hol", binary])
        .output()?;
    assert!(
        output.status.success(),
        "stderr: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8(output.stdout)?;
    assert!(stdout.contains("kind\tnative-signed-hol-round-trip\n"));
    assert!(stdout.contains("statement\t(lambda x:bool. x) true = true\n"));
    assert!(stdout.contains("signature-authenticated"));
    assert!(stdout.contains("signer-pinned"));
    assert!(stdout.contains("theorem-read"));
    assert!(stdout.contains("imported_theorem\t0\t8\n"));
    assert!(stdout.contains("native_exit\tsuccess\n"));
    assert!(stdout.contains("native_endpoint_cleanup\tremoved\n"));
    Ok(())
}

#[test]
fn coordinator_cleans_only_the_dead_endpoint_after_a_pending_call_fails() -> Result<()> {
    let Some(binary) = binary() else {
        return Ok(());
    };
    let directory: Repl<()> = Repl::empty()?;
    let survivor = directory.register_kernel("test", Some("survivor"), &[9; 32])?;

    let mut process = NativeKernelProcess::spawn(binary)?;
    let description = process.describe()?;
    let identity = description.identity();
    let dead =
        directory.register_kernel("stdio", Some(binary), &description.identity().public_key())?;
    let expected = directory.expected_kernel_identity(dead)?;
    let initiator = SessionInitiator::begin(
        ServiceIdentity::new(expected.signer(), *expected.public_key())?,
        &description,
    )?;
    let accepted = process.open_session(initiator.request())?;
    let mut session = initiator.accept(&accepted)?;
    let pending = session.command(ServiceOperation::OpenHol)?;

    assert!(!process.kill()?.success());
    assert!(process.execute(&pending).is_err());
    drop(process);
    directory.unregister_kernel(dead)?;

    assert!(directory.expected_kernel_identity(dead).is_err());
    assert_eq!(
        directory.expected_kernel_identity(survivor)?.public_key(),
        &[9; 32]
    );
    assert!(directory.connections()?.is_empty());
    assert_ne!(
        identity.signer(),
        directory.expected_kernel_identity(survivor)?.signer()
    );
    Ok(())
}
