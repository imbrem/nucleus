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
        /// Canonical cross-language identity of every reserved surface node.
        #[derive(Clone, Copy, Eq, PartialEq)]
        #[repr(u64)]
        pub enum SurfaceTag {
            $( $variant = $id, )+
        }

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

// Keep groups in semantic order. Gaps leave room to grow one group without
// mixing core syntax, definitions, and macros in cross-language tables.
surface_tags! {
    // HolE constructors and surface imports.
    TyBool = 0 => "TY_BOOL",
    TyArr = 1 => "TY_ARR",
    TyApp = 2 => "TY_APP",
    TyLam = 3 => "TY_LAM",
    TyBv = 4 => "TY_BV",
    TySub = 5 => "TY_SUB",
    TyExists = 6 => "TY_EXISTS",
    TyModel = 7 => "TY_MODEL",
    TyPrim = 8 => "TY_PRIM",
    TyImport = 9 => "TY_IMPORT",
    TmPrim = 10 => "TM_PRIM",
    TmBv = 11 => "TM_BV",
    TmFv = 12 => "TM_FV",
    TmApp = 13 => "TM_APP",
    TmLam = 14 => "TM_LAM",
    TmBool = 15 => "TM_BOOL",
    TmEq = 16 => "TM_EQ",
    TmEps = 17 => "TM_EPS",
    TmAbs = 18 => "TM_ABS",
    TmRep = 19 => "TM_REP",
    TmImport = 20 => "TM_IMPORT",

    // Type definitions.
    TyUnit = 64 => "TY_UNIT",
    TyNat = 65 => "TY_NAT",
    TyBlob = 66 => "TY_BLOB",
    TyInt = 67 => "TY_INT",
    TyI8 = 68 => "TY_I8",
    TyI16 = 69 => "TY_I16",
    TyI32 = 70 => "TY_I32",
    TyI64 = 71 => "TY_I64",
    TyV128 = 72 => "TY_V128",
    TyChar = 73 => "TY_CHAR",
    TyString = 74 => "TY_STRING",
    TyF32 = 75 => "TY_F32",
    TyF64 = 76 => "TY_F64",
    TyList = 77 => "TY_LIST",
    TyResult = 78 => "TY_RESULT",
    TyOption = 79 => "TY_OPTION",
    TyDict = 80 => "TY_DICT",
    TyFset = 81 => "TY_FSET",
    TyFbag = 82 => "TY_FBAG",

    // Context macros.
    TmSetAnd = 128 => "TM_SET_AND",
    TmSetOr = 129 => "TM_SET_OR",

    // Literal macros.
    TmLitUnit = 144 => "TM_LIT_UNIT",
    TmLitNat = 145 => "TM_LIT_NAT",
    TmLitBlob = 146 => "TM_LIT_BLOB",
    TmLitInt = 147 => "TM_LIT_INT",
    TmLitI8 = 148 => "TM_LIT_I8",
    TmLitI16 = 149 => "TM_LIT_I16",
    TmLitI32 = 150 => "TM_LIT_I32",
    TmLitI64 = 151 => "TM_LIT_I64",
    TmLitV128 = 152 => "TM_LIT_V128",
    TmLitChar = 153 => "TM_LIT_CHAR",
    TmLitString = 154 => "TM_LIT_STRING",
    TmLitF32 = 155 => "TM_LIT_F32",
    TmLitF64 = 156 => "TM_LIT_F64",
    TmLitList = 157 => "TM_LIT_LIST",
    TmLitResult = 158 => "TM_LIT_RESULT",
    TmLitOption = 159 => "TM_LIT_OPTION",
    TmLitDict = 160 => "TM_LIT_DICT",
    TmLitFset = 161 => "TM_LIT_FSET",
    TmLitFbag = 162 => "TM_LIT_FBAG",

    // Natural and integer definitions.
    TmNatAdd = 256 => "TM_NAT_ADD",
    TmNatSub = 257 => "TM_NAT_SUB",
    TmNatMul = 258 => "TM_NAT_MUL",
    TmNatDiv = 259 => "TM_NAT_DIV",
    TmNatMod = 260 => "TM_NAT_MOD",
    TmNatPow = 261 => "TM_NAT_POW",
    TmNatLe = 262 => "TM_NAT_LE",
    TmNatLt = 263 => "TM_NAT_LT",
    TmNatCmp = 264 => "TM_NAT_CMP",
    TmIntAdd = 265 => "TM_INT_ADD",
    TmIntSub = 266 => "TM_INT_SUB",
    TmIntMul = 267 => "TM_INT_MUL",
    TmIntDiv = 268 => "TM_INT_DIV",
    TmIntMod = 269 => "TM_INT_MOD",
    TmIntNeg = 270 => "TM_INT_NEG",
    TmIntAbs = 271 => "TM_INT_ABS",
    TmIntPow = 272 => "TM_INT_POW",
    TmIntLe = 273 => "TM_INT_LE",
    TmIntLt = 274 => "TM_INT_LT",
    TmIntCmp = 275 => "TM_INT_CMP",

    // Blob, character, and string definitions.
    TmBlobAt = 288 => "TM_BLOB_AT",
    TmBlobLen = 289 => "TM_BLOB_LEN",
    TmBlobSlice = 290 => "TM_BLOB_SLICE",
    TmBlobCat = 291 => "TM_BLOB_CAT",
    TmBlobLe = 292 => "TM_BLOB_LE",
    TmBlobLt = 293 => "TM_BLOB_LT",
    TmBlobCmp = 294 => "TM_BLOB_CMP",
    TmCharToNat = 295 => "TM_CHAR_TO_NAT",
    TmCharFromNat = 296 => "TM_CHAR_FROM_NAT",
    TmCharLe = 297 => "TM_CHAR_LE",
    TmCharLt = 298 => "TM_CHAR_LT",
    TmCharCmp = 299 => "TM_CHAR_CMP",
    TmStringAt = 300 => "TM_STRING_AT",
    TmStringLen = 301 => "TM_STRING_LEN",
    TmStringSlice = 302 => "TM_STRING_SLICE",
    TmStringCat = 303 => "TM_STRING_CAT",
    TmStringLe = 304 => "TM_STRING_LE",
    TmStringLt = 305 => "TM_STRING_LT",
    TmStringCmp = 306 => "TM_STRING_CMP",

    // Fixed-width integer and vector definitions. Width is supplied by type.
    TmIAdd = 320 => "TM_I_ADD",
    TmISub = 321 => "TM_I_SUB",
    TmIMul = 322 => "TM_I_MUL",
    TmIDivS = 323 => "TM_I_DIV_S",
    TmIDivU = 324 => "TM_I_DIV_U",
    TmIRemS = 325 => "TM_I_REM_S",
    TmIRemU = 326 => "TM_I_REM_U",
    TmIAnd = 327 => "TM_I_AND",
    TmIOr = 328 => "TM_I_OR",
    TmIXor = 329 => "TM_I_XOR",
    TmIShl = 330 => "TM_I_SHL",
    TmIShrS = 331 => "TM_I_SHR_S",
    TmIShrU = 332 => "TM_I_SHR_U",
    TmIRotl = 333 => "TM_I_ROTL",
    TmIRotr = 334 => "TM_I_ROTR",
    TmILeS = 335 => "TM_I_LE_S",
    TmILeU = 336 => "TM_I_LE_U",
    TmILtS = 337 => "TM_I_LT_S",
    TmILtU = 338 => "TM_I_LT_U",
    TmV128And = 339 => "TM_V128_AND",
    TmV128Or = 340 => "TM_V128_OR",
    TmV128Xor = 341 => "TM_V128_XOR",
    TmV128Not = 342 => "TM_V128_NOT",

    // Floating-point definitions. Width is supplied by type.
    TmFAdd = 352 => "TM_F_ADD",
    TmFSub = 353 => "TM_F_SUB",
    TmFMul = 354 => "TM_F_MUL",
    TmFDiv = 355 => "TM_F_DIV",
    TmFNeg = 356 => "TM_F_NEG",
    TmFAbs = 357 => "TM_F_ABS",
    TmFSqrt = 358 => "TM_F_SQRT",
    TmFMin = 359 => "TM_F_MIN",
    TmFMax = 360 => "TM_F_MAX",
    TmFCeil = 361 => "TM_F_CEIL",
    TmFFloor = 362 => "TM_F_FLOOR",
    TmFTrunc = 363 => "TM_F_TRUNC",
    TmFNearest = 364 => "TM_F_NEAREST",
    TmFLe = 365 => "TM_F_LE",
    TmFLt = 366 => "TM_F_LT",

    // Algebraic and finite-collection definitions.
    TmListLen = 384 => "TM_LIST_LEN",
    TmListAt = 385 => "TM_LIST_AT",
    TmListSlice = 386 => "TM_LIST_SLICE",
    TmListCat = 387 => "TM_LIST_CAT",
    TmResultOk = 388 => "TM_RESULT_OK",
    TmResultErr = 389 => "TM_RESULT_ERR",
    TmResultIsOk = 390 => "TM_RESULT_IS_OK",
    TmResultUnwrapOk = 391 => "TM_RESULT_UNWRAP_OK",
    TmResultUnwrapErr = 392 => "TM_RESULT_UNWRAP_ERR",
    TmOptionNone = 393 => "TM_OPTION_NONE",
    TmOptionSome = 394 => "TM_OPTION_SOME",
    TmOptionIsSome = 395 => "TM_OPTION_IS_SOME",
    TmOptionUnwrap = 396 => "TM_OPTION_UNWRAP",
    TmDictEmpty = 397 => "TM_DICT_EMPTY",
    TmDictInsert = 398 => "TM_DICT_INSERT",
    TmDictRemove = 399 => "TM_DICT_REMOVE",
    TmDictGet = 400 => "TM_DICT_GET",
    TmDictContains = 401 => "TM_DICT_CONTAINS",
    TmDictLen = 402 => "TM_DICT_LEN",
    TmFsetEmpty = 403 => "TM_FSET_EMPTY",
    TmFsetInsert = 404 => "TM_FSET_INSERT",
    TmFsetRemove = 405 => "TM_FSET_REMOVE",
    TmFsetContains = 406 => "TM_FSET_CONTAINS",
    TmFsetUnion = 407 => "TM_FSET_UNION",
    TmFsetIntersection = 408 => "TM_FSET_INTERSECTION",
    TmFsetDifference = 409 => "TM_FSET_DIFFERENCE",
    TmFsetLen = 410 => "TM_FSET_LEN",
    TmFbagEmpty = 411 => "TM_FBAG_EMPTY",
    TmFbagInsert = 412 => "TM_FBAG_INSERT",
    TmFbagRemove = 413 => "TM_FBAG_REMOVE",
    TmFbagCount = 414 => "TM_FBAG_COUNT",
    TmFbagUnion = 415 => "TM_FBAG_UNION",
    TmFbagSum = 416 => "TM_FBAG_SUM",
    TmFbagIntersection = 417 => "TM_FBAG_INTERSECTION",
    TmFbagDifference = 418 => "TM_FBAG_DIFFERENCE",
    TmFbagLen = 419 => "TM_FBAG_LEN",
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

impl SurfaceTag {
    #[must_use]
    pub const fn is_supported(self) -> bool {
        matches!(
            self,
            Self::TyBool
                | Self::TyArr
                | Self::TyImport
                | Self::TmBv
                | Self::TmFv
                | Self::TmApp
                | Self::TmLam
                | Self::TmBool
                | Self::TmEq
                | Self::TmImport
                | Self::TyNat
                | Self::TmLitNat
        )
    }
}
