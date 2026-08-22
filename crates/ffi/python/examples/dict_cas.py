"""Resolve a checked CAS fact through an entirely Python-defined provider."""

from covalence.cas import CasAssertion, CasFact, CasNotFoundError, get_exact
from covalence.lib.hash import O256


class DictCas:
    """The provider owns plain bytes and may implement any userspace policy."""

    def __init__(self, blobs: dict[O256, bytes]) -> None:
        self._blobs = blobs

    def get(self, address: O256) -> CasFact:
        try:
            blob = self._blobs[address]
        except KeyError as error:
            raise CasNotFoundError(str(address)) from error

        # Raw dictionary bytes are untrusted. The only route to CasFact checks
        # every byte against the requested address in Rust.
        return CasAssertion(address, blob).try_into()


payload = b"arbitrary Python CAS logic"
expected = O256.hash(payload)
provider = DictCas({expected: payload})
fact = get_exact(provider, expected)

assert fact.hash == expected
assert fact.blob == payload
print(f"resolved {fact.hash} ({len(fact.blob)} bytes)")
