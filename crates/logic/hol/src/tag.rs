use std::error::Error;
use std::fmt::{self, Display, Formatter};
use std::str::FromStr;

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum UnknownSurfaceTag {
    Integer(u64),
    Name(String),
}

impl Display for UnknownSurfaceTag {
    fn fmt(&self, formatter: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Self::Integer(id) => write!(formatter, "unknown surface tag integer {id}"),
            Self::Name(name) => write!(formatter, "unknown surface tag name {name:?}"),
        }
    }
}

impl Error for UnknownSurfaceTag {}

macro_rules! surface_tags {
    ($( $variant:ident = $id:literal => $name:literal, )+) => {
        #[derive(Clone, Copy, Eq, PartialEq)]
        #[repr(u64)]
        pub enum SurfaceTag { $( $variant = $id, )+ }

        impl SurfaceTag {
            pub const ALL: &'static [Self] = &[$( Self::$variant, )+];
        }

        impl From<SurfaceTag> for u64 {
            fn from(tag: SurfaceTag) -> Self { tag as Self }
        }

        impl From<SurfaceTag> for &'static str {
            fn from(tag: SurfaceTag) -> Self {
                match tag { $( SurfaceTag::$variant => $name, )+ }
            }
        }

        impl TryFrom<u64> for SurfaceTag {
            type Error = UnknownSurfaceTag;

            fn try_from(id: u64) -> Result<Self, Self::Error> {
                match id {
                    $( $id => Ok(Self::$variant), )+
                    _ => Err(UnknownSurfaceTag::Integer(id)),
                }
            }
        }

        impl FromStr for SurfaceTag {
            type Err = UnknownSurfaceTag;

            fn from_str(name: &str) -> Result<Self, Self::Err> {
                match name {
                    $( $name => Ok(Self::$variant), )+
                    _ => Err(UnknownSurfaceTag::Name(name.into())),
                }
            }
        }
    };
}

surface_tags! {
    KindStar = 0 => "KIND_STAR",
    KindArr = 1 => "KIND_ARR",

    // Every HolE constructor.
    TyBool = 2 => "TY_BOOL",
    TyArr = 3 => "TY_ARR",
    TyApp = 4 => "TY_APP",
    TyLam = 5 => "TY_LAM",
    TyBv = 6 => "TY_BV",
    TySub = 7 => "TY_SUB",
    TyExists = 8 => "TY_EXISTS",
    TyModel = 9 => "TY_MODEL",
    TyPrim = 10 => "TY_PRIM",
    TyLink = 11 => "TY_LINK",
    TmPrim = 12 => "TM_PRIM",
    TmBv = 13 => "TM_BV",
    TmFv = 14 => "TM_FV",
    TmApp = 15 => "TM_APP",
    TmLam = 16 => "TM_LAM",
    TmBool = 17 => "TM_BOOL",
    TmEq = 18 => "TM_EQ",
    TmEps = 19 => "TM_EPS",
    TmAbs = 20 => "TM_ABS",
    TmRep = 21 => "TM_REP",

    // Surface judgement/context forms and definitions needed by the first demo.
    TmLink = 22 => "TM_LINK",
    Imp = 64 => "IMP",
    TyNat = 65 => "TY_NAT",
    Ctx = 66 => "CTX",
    TmLitNat = 67 => "TM_LIT_NAT",
}

impl TryFrom<&str> for SurfaceTag {
    type Error = UnknownSurfaceTag;

    fn try_from(name: &str) -> Result<Self, Self::Error> {
        name.parse()
    }
}

impl Display for SurfaceTag {
    fn fmt(&self, formatter: &mut Formatter<'_>) -> fmt::Result {
        formatter.write_str((*self).into())
    }
}

impl fmt::Debug for SurfaceTag {
    fn fmt(&self, formatter: &mut Formatter<'_>) -> fmt::Result {
        Display::fmt(self, formatter)
    }
}
