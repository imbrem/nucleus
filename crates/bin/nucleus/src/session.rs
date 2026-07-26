use std::fmt;

use covalence_data_sexpr::{SExpr, Symbol, sax::FromEvents, text};
use covalence_nucleus::{
    Def, KnowledgeError, KnowledgeModel, SuccessfulTraceQuery, TermIdentity, TraceOutcome,
    TraceStep, TrustedDb,
};

pub struct Session {
    database: TrustedDb,
}

impl Session {
    pub fn new() -> Result<Self, Error> {
        let mut database = TrustedDb::create_in_memory().map_err(Error::Database)?;
        database
            .install_knowledge_model()
            .map_err(Error::Knowledge)?;
        Ok(Self { database })
    }

    pub fn eval(&mut self, input: &str) -> Result<String, Error> {
        let command = parse_expression(input)?;
        let list = command
            .as_list()
            .ok_or_else(|| Error::invalid("command must be a list"))?;
        let Some(name) = list.first().and_then(SExpr::as_atom).map(Symbol::as_str) else {
            return Err(Error::invalid("command must start with an atom"));
        };
        match (name, &list[1..]) {
            ("type", [name, definition]) => {
                let name = atom(name, "type name")?;
                let definition = print_expression(definition);
                let id = self
                    .database
                    .knowledge_model()
                    .map_err(Error::Knowledge)?
                    .define_type(name, &definition)
                    .map_err(Error::Knowledge)?;
                Ok(format!("(defined type {name} {})", id.get()))
            }
            ("term", [name, r#type, definition]) => {
                let name = atom(name, "term name")?;
                let type_name = atom(r#type, "type name")?;
                let definition = print_expression(definition);
                let mut model = self.database.knowledge_model().map_err(Error::Knowledge)?;
                let type_id = model
                    .type_named(type_name)
                    .map_err(Error::Knowledge)?
                    .ok_or_else(|| Error::unknown("type", type_name))?;
                let id = model
                    .define_term(name, type_id.use_id(), &definition)
                    .map_err(Error::Knowledge)?;
                Ok(format!("(defined term {name} {})", id.get()))
            }
            ("executor", [name]) => {
                let name = atom(name, "executor name")?;
                let id = self
                    .database
                    .knowledge_model()
                    .map_err(Error::Knowledge)?
                    .register_executor(name)
                    .map_err(Error::Knowledge)?;
                Ok(format!("(defined executor {name} {})", id.get()))
            }
            ("trace", [executor, program, input, output]) => {
                let executor_name = atom(executor, "executor name")?;
                let program_name = atom(program, "program term")?;
                let input_name = atom(input, "input term")?;
                let output_name = atom(output, "output term")?;
                let mut model = self.database.knowledge_model().map_err(Error::Knowledge)?;
                let executor = model
                    .executor_named(executor_name)
                    .map_err(Error::Knowledge)?
                    .ok_or_else(|| Error::unknown("executor", executor_name))?;
                let program = required_term(&model, program_name)?;
                let input = required_term(&model, input_name)?;
                let output = required_term(&model, output_name)?;
                let trace = model
                    .record_trace(
                        executor,
                        program.use_id(),
                        input.use_id(),
                        Some(output.use_id()),
                        TraceOutcome::Returned,
                    )
                    .map_err(Error::Knowledge)?;
                model
                    .record_step(TraceStep {
                        trace: trace.use_id(),
                        ordinal: 0,
                        operation: program.use_id(),
                        before: input.use_id(),
                        after: output.use_id(),
                    })
                    .map_err(Error::Knowledge)?;
                Ok(format!("(recorded trace {})", trace.get()))
            }
            ("outputs", [program]) => {
                let program_name = atom(program, "program term")?;
                let model = self.database.knowledge_model().map_err(Error::Knowledge)?;
                let program = required_term(&model, program_name)?;
                let outputs = model
                    .query_successful_traces(SuccessfulTraceQuery::for_program(program.use_id()))
                    .map_err(Error::Knowledge)?;
                let names = outputs
                    .into_iter()
                    .map(|row| model.term_name(row.output).map_err(Error::Knowledge))
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(format!("({})", names.join(" ")))
            }
            (unknown, _)
                if !matches!(unknown, "type" | "term" | "executor" | "trace" | "outputs") =>
            {
                Err(Error::UnknownCommand(unknown.to_owned()))
            }
            _ => Err(Error::invalid(format!("wrong arguments for `{name}`"))),
        }
    }
}

#[derive(Debug)]
pub enum Error {
    Database(covalence_nucleus::TrustedDbError),
    Knowledge(KnowledgeError),
    Syntax(text::Error),
    Structure(covalence_data_sexpr::sax::BuildError),
    UnknownCommand(String),
    UnknownName {
        namespace: &'static str,
        name: String,
    },
    InvalidCommand(String),
}

impl Error {
    fn unknown(namespace: &'static str, name: &str) -> Self {
        Self::UnknownName {
            namespace,
            name: name.to_owned(),
        }
    }

    fn invalid(reason: impl Into<String>) -> Self {
        Self::InvalidCommand(reason.into())
    }
}

impl fmt::Display for Error {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Database(source) => write!(formatter, "database setup failed: {source}"),
            Self::Knowledge(source) => write!(formatter, "knowledge operation failed: {source}"),
            Self::Syntax(source) => write!(formatter, "invalid command syntax: {source}"),
            Self::Structure(source) => write!(formatter, "invalid command structure: {source}"),
            Self::UnknownCommand(command) => write!(formatter, "unknown command `{command}`"),
            Self::UnknownName { namespace, name } => {
                write!(formatter, "unknown {namespace} `{name}`")
            }
            Self::InvalidCommand(reason) => write!(formatter, "invalid command: {reason}"),
        }
    }
}

impl std::error::Error for Error {}

fn parse_expression(input: &str) -> Result<SExpr, Error> {
    let events = text::parse_symbols(input)
        .collect::<Result<Vec<_>, _>>()
        .map_err(Error::Syntax)?;
    SExpr::from_events(events).map_err(Error::Structure)
}

fn print_expression(expression: &SExpr) -> String {
    match expression {
        SExpr::Atom(atom) => {
            let text = atom.as_str();
            if text.is_empty()
                || text
                    .chars()
                    .any(|character| character.is_whitespace() || "()\";".contains(character))
            {
                format!("\"{}\"", text.replace('\\', "\\\\").replace('"', "\\\""))
            } else {
                text.to_owned()
            }
        }
        SExpr::List(children) => format!(
            "({})",
            children
                .iter()
                .map(print_expression)
                .collect::<Vec<_>>()
                .join(" ")
        ),
    }
}

fn atom<'a>(expression: &'a SExpr, role: &str) -> Result<&'a str, Error> {
    expression
        .as_atom()
        .map(Symbol::as_str)
        .ok_or_else(|| Error::invalid(format!("{role} must be an atom")))
}

fn required_term(model: &KnowledgeModel<'_>, name: &str) -> Result<Def<TermIdentity>, Error> {
    model
        .term_named(name)
        .map_err(Error::Knowledge)?
        .ok_or_else(|| Error::unknown("term", name))
}

#[cfg(test)]
mod tests {
    use super::Session;

    #[test]
    fn session_reaches_the_existential_trace_query() {
        let mut session = Session::new().unwrap();
        session.eval("(type Value (value-type))").unwrap();
        session.eval("(term add Value (add 20 22))").unwrap();
        session.eval("(term nil Value ())").unwrap();
        session.eval("(term forty-two Value 42)").unwrap();
        session.eval("(executor evaluator)").unwrap();
        session.eval("(trace evaluator add nil forty-two)").unwrap();

        assert_eq!(session.eval("(outputs add)").unwrap(), "(forty-two)");
    }

    #[test]
    fn absence_is_empty_and_names_do_not_silently_rebind() {
        let mut session = Session::new().unwrap();
        session.eval("(type Value (value-type))").unwrap();
        assert!(session.eval("(type Value (different-type))").is_err());
        session.eval("(term add Value (add 20 22))").unwrap();
        session.eval("(term nil Value ())").unwrap();
        session.eval("(term forty-two Value 42)").unwrap();
        assert_eq!(session.eval("(outputs add)").unwrap(), "()");
        assert!(session.eval("(trace missing add nil forty-two)").is_err());
    }
}
