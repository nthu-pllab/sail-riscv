/*=======================================================================================*/
/*  This Sail RISC-V architecture model, comprising all files and                        */
/*  directories except where otherwise noted is subject the BSD                          */
/*  two-clause license in the LICENSE file.                                              */
/*                                                                                       */
/*  SPDX-License-Identifier: BSD-2-Clause                                                */
/*=======================================================================================*/

/* Basic type and function definitions used pervasively in the model. */

/* ISA extension names as enums */
scattered enum extension

// Function used to determine if an extension is enabled in the current configuration.
// This means an extension is implemented & supported, *and* any necessary bits
// are set in the relevant CSRs (misa, mstatus, etc.) to enable its use. It is possible
// for some extensions to be supported in hardware, but temporarily disabled via a CSR,
// in which case this function should return false.
val extensionEnabled : extension -> bool
scattered function extensionEnabled

/* this value is only defined for the runtime platform for ELF loading
 * checks, and not used in the model.
 */
let xlen_val = sizeof(xlen)

let xlen_max_unsigned = 2 ^ sizeof(xlen) - 1
let xlen_max_signed = 2 ^ (sizeof(xlen) - 1) - 1
let xlen_min_signed = 0 - 2 ^ (sizeof(xlen) - 1)

type half = bits(16)
type word = bits(32)

/* register identifiers */

type regidx  = bits(5)
type cregidx = bits(3)    /* identifiers in RVC instructions */
type csreg   = bits(12)   /* CSR addressing */

/* register file indexing */

type regno = range(0, 31)

function regidx_to_regno (b : regidx) -> regno = unsigned(b)

/* mapping RVC register indices into normal indices */
val creg2reg_idx : cregidx -> regidx
function creg2reg_idx(creg) = 0b01 @ creg

/* some architecture and ABI relevant register identifiers */
let zreg : regidx = 0b00000  /* x0, zero register  */
let ra   : regidx = 0b00001  /* x1, return address */
let sp   : regidx = 0b00010  /* x2, stack pointer  */

/* instruction fields */

type opcode = bits(7)
type imm12  = bits(12)
type imm20  = bits(20)
type amo    = bits(1)  /* amo opcode flags */

/* base architecture definitions */

enum Architecture = {RV32, RV64, RV128}
type arch_xlen = bits(2)
function architecture(a : arch_xlen) -> option(Architecture) =
  match (a) {
    0b01 => Some(RV32),
    0b10 => Some(RV64),
    0b11 => Some(RV128),
    _    => None()
  }

function arch_to_bits(a : Architecture) -> arch_xlen =
  match (a) {
    RV32  => 0b01,
    RV64  => 0b10,
    RV128 => 0b11
  }


/* model-internal exceptions */

union exception = {
  Error_not_implemented : string,
  Error_internal_error  : unit
}

val not_implemented : forall ('a : Type). string -> 'a
function not_implemented message = throw(Error_not_implemented(message))

val internal_error : forall ('a : Type). (string, int, string) -> 'a
function internal_error(file, line, s) = {
    assert (false, file ^ ":" ^ dec_str(line) ^ ": " ^ s);
    throw Error_internal_error()
}

/* privilege levels */

type priv_level = bits(2)
enum Privilege  = {User, Supervisor, Machine}

val privLevel_to_bits : Privilege -> priv_level
function privLevel_to_bits (p) =
  match (p) {
    User       => 0b00,
    Supervisor => 0b01,
    Machine    => 0b11
  }

/*!
 * Converts the given 2-bit privilege level code to the [Privilege] enum.
 * Calling with a reserved code will result in an internal error.
 */
val privLevel_of_bits : priv_level -> Privilege
function privLevel_of_bits (p) =
  match (p) {
    0b00 => User,
    0b01 => Supervisor,
    0b11 => Machine,
    0b10 => internal_error(__FILE__, __LINE__, "Invalid privilege level: " ^ BitStr(p))
  }

val privLevel_to_str : Privilege -> string
function privLevel_to_str (p) =
  match (p) {
    User       => "U",
    Supervisor => "S",
    Machine    => "M"
  }

overload to_str = {privLevel_to_str}

/* enum denoting whether an executed instruction retires */

enum Retired = {RETIRE_SUCCESS, RETIRE_FAIL}

/* memory access types */

union AccessType ('a : Type) = {
  Read      : 'a,
  Write     : 'a,
  ReadWrite : ('a, 'a),
  Execute   : unit
}

enum word_width = {BYTE, HALF, WORD, DOUBLE}

/* architectural interrupt definitions */

enum InterruptType = {
  I_U_Software,
  I_S_Software,
  I_M_Software,
  I_U_Timer,
  I_S_Timer,
  I_M_Timer,
  I_U_External,
  I_S_External,
  I_M_External
}

val interruptType_to_bits : InterruptType -> exc_code
function interruptType_to_bits (i) =
  match (i) {
    I_U_Software => 0x00,
    I_S_Software => 0x01,
    I_M_Software => 0x03,
    I_U_Timer    => 0x04,
    I_S_Timer    => 0x05,
    I_M_Timer    => 0x07,
    I_U_External => 0x08,
    I_S_External => 0x09,
    I_M_External => 0x0b
  }

/* architectural exception definitions */

union ExceptionType = {
 E_Fetch_Addr_Align   : unit,
 E_Fetch_Access_Fault : unit,
 E_Illegal_Instr      : unit,
 E_Breakpoint         : unit,
 E_Load_Addr_Align    : unit,
 E_Load_Access_Fault  : unit,
 E_SAMO_Addr_Align    : unit,
 E_SAMO_Access_Fault  : unit,
 E_U_EnvCall          : unit,
 E_S_EnvCall          : unit,
 E_Reserved_10        : unit,
 E_M_EnvCall          : unit,
 E_Fetch_Page_Fault   : unit,
 E_Load_Page_Fault    : unit,
 E_Reserved_14        : unit,
 E_SAMO_Page_Fault    : unit,

 /* extensions */
 E_Extension          : ext_exc_type
}

val exceptionType_to_bits : ExceptionType -> exc_code
function exceptionType_to_bits(e) =
  match (e) {
    E_Fetch_Addr_Align()   => 0x00,
    E_Fetch_Access_Fault() => 0x01,
    E_Illegal_Instr()      => 0x02,
    E_Breakpoint()         => 0x03,
    E_Load_Addr_Align()    => 0x04,
    E_Load_Access_Fault()  => 0x05,
    E_SAMO_Addr_Align()    => 0x06,
    E_SAMO_Access_Fault()  => 0x07,
    E_U_EnvCall()          => 0x08,
    E_S_EnvCall()          => 0x09,
    E_Reserved_10()        => 0x0a,
    E_M_EnvCall()          => 0x0b,
    E_Fetch_Page_Fault()   => 0x0c,
    E_Load_Page_Fault()    => 0x0d,
    E_Reserved_14()        => 0x0e,
    E_SAMO_Page_Fault()    => 0x0f,

    /* extensions */
    E_Extension(e)         => ext_exc_type_to_bits(e)
  }

val num_of_ExceptionType : ExceptionType -> {'n, (0 <= 'n < xlen). int('n)}
function num_of_ExceptionType(e) =
  match (e) {
    E_Fetch_Addr_Align()   => 0,
    E_Fetch_Access_Fault() => 1,
    E_Illegal_Instr()      => 2,
    E_Breakpoint()         => 3,
    E_Load_Addr_Align()    => 4,
    E_Load_Access_Fault()  => 5,
    E_SAMO_Addr_Align()    => 6,
    E_SAMO_Access_Fault()  => 7,
    E_U_EnvCall()          => 8,
    E_S_EnvCall()          => 9,
    E_Reserved_10()        => 10,
    E_M_EnvCall()          => 11,
    E_Fetch_Page_Fault()   => 12,
    E_Load_Page_Fault()    => 13,
    E_Reserved_14()        => 14,
    E_SAMO_Page_Fault()    => 15,

    /* extensions */
    E_Extension(e)         => num_of_ext_exc_type(e)

  }

val exceptionType_to_str : ExceptionType -> string
function exceptionType_to_str(e) =
  match (e) {
    E_Fetch_Addr_Align()   => "misaligned-fetch",
    E_Fetch_Access_Fault() => "fetch-access-fault",
    E_Illegal_Instr()      => "illegal-instruction",
    E_Breakpoint()         => "breakpoint",
    E_Load_Addr_Align()    => "misaligned-load",
    E_Load_Access_Fault()  => "load-access-fault",
    E_SAMO_Addr_Align()    => "misaligned-store/amo",
    E_SAMO_Access_Fault()  => "store/amo-access-fault",
    E_U_EnvCall()          => "u-call",
    E_S_EnvCall()          => "s-call",
    E_Reserved_10()        => "reserved-0",
    E_M_EnvCall()          => "m-call",
    E_Fetch_Page_Fault()   => "fetch-page-fault",
    E_Load_Page_Fault()    => "load-page-fault",
    E_Reserved_14()        => "reserved-1",
    E_SAMO_Page_Fault()    => "store/amo-page-fault",

    /* extensions */
    E_Extension(e)         => ext_exc_type_to_str(e)
  }

overload to_str = {exceptionType_to_str}

/* trap modes */

type tv_mode = bits(2)
enum TrapVectorMode = {TV_Direct, TV_Vector, TV_Reserved}

val trapVectorMode_of_bits : tv_mode -> TrapVectorMode
function trapVectorMode_of_bits (m) =
  match (m) {
    0b00 => TV_Direct,
    0b01 => TV_Vector,
    _    => TV_Reserved
  }

/* extension context status */

type ext_status = bits(2)
enum ExtStatus = {Off, Initial, Clean, Dirty}

val extStatus_to_bits : ExtStatus -> ext_status
function extStatus_to_bits(e) =
  match (e) {
    Off     => 0b00,
    Initial => 0b01,
    Clean   => 0b10,
    Dirty   => 0b11
  }

val extStatus_of_bits : ext_status -> ExtStatus
function extStatus_of_bits(e) =
  match (e) {
    0b00 => Off,
    0b01 => Initial,
    0b10 => Clean,
    0b11 => Dirty
  }

/* supervisor-level address translation modes */

type satp_mode = bits(4)
enum SATPMode = {Sbare, Sv32, Sv39, Sv48}

function satp64Mode_of_bits(a : Architecture, m : satp_mode) -> option(SATPMode) =
  match (a, m) {
    (_,    0x0) => Some(Sbare),
    (RV32, 0x1) => Some(Sv32),
    (RV64, 0x8) => Some(Sv39),
    (RV64, 0x9) => Some(Sv48),
    (_, _)      => None()
  }

/* CSR access control bits (from CSR addresses) */

type csrRW = bits(2)  /* read/write */

/* instruction opcode grouping */
enum uop = {RISCV_LUI, RISCV_AUIPC}               /* upper immediate ops */
enum bop = {RISCV_BEQ, RISCV_BNE, RISCV_BLT,
            RISCV_BGE, RISCV_BLTU, RISCV_BGEU}    /* branch ops */
enum iop = {RISCV_ADDI, RISCV_SLTI, RISCV_SLTIU,
            RISCV_XORI, RISCV_ORI, RISCV_ANDI}    /* immediate ops */
enum sop = {RISCV_SLLI, RISCV_SRLI, RISCV_SRAI}   /* shift ops */
enum rop = {RISCV_ADD, RISCV_SUB, RISCV_SLL, RISCV_SLT,
            RISCV_SLTU, RISCV_XOR, RISCV_SRL, RISCV_SRA,
            RISCV_OR, RISCV_AND}                  /* reg-reg ops */

enum ropw  = {RISCV_ADDW, RISCV_SUBW, RISCV_SLLW,
              RISCV_SRLW, RISCV_SRAW}             /* reg-reg 32-bit ops */
enum sopw = {RISCV_SLLIW, RISCV_SRLIW,
             RISCV_SRAIW}                         /* RV64-only shift ops */
enum amoop = {AMOSWAP, AMOADD, AMOXOR, AMOAND, AMOOR,
              AMOMIN, AMOMAX, AMOMINU, AMOMAXU}   /* AMO ops */
enum csrop = {CSRRW, CSRRS, CSRRC}                /* CSR ops */

enum cbop_zicbom = {CBO_CLEAN, CBO_FLUSH, CBO_INVAL}  /* Zicbom ops */

enum brop_zba = {RISCV_SH1ADD, RISCV_SH2ADD, RISCV_SH3ADD}

enum brop_zbb = {RISCV_ANDN, RISCV_ORN, RISCV_XNOR, RISCV_MAX,
                 RISCV_MAXU, RISCV_MIN, RISCV_MINU, RISCV_ROL,
                 RISCV_ROR}

enum brop_zbkb = {RISCV_PACK, RISCV_PACKH}

enum brop_zbs = {RISCV_BCLR, RISCV_BEXT, RISCV_BINV, RISCV_BSET}

enum bropw_zba = {RISCV_ADDUW, RISCV_SH1ADDUW, RISCV_SH2ADDUW,
                  RISCV_SH3ADDUW}

enum bropw_zbb = {RISCV_ROLW, RISCV_RORW}

enum biop_zbs = {RISCV_BCLRI, RISCV_BEXTI, RISCV_BINVI, RISCV_BSETI}

enum extop_zbb = {RISCV_SEXTB, RISCV_SEXTH, RISCV_ZEXTH}

enum zicondop = {RISCV_CZERO_EQZ, RISCV_CZERO_NEZ}

enum psimple = {CLS, CLSW, ABS, ABSW, REV, REV8, REV16}

enum pshift_left_b = {PSLLI_B}

enum pshift_left_h = {PSLLI_H, PSSLAI_H}

enum pshift_left_w_rv32 = {SSLAI}

enum pshift_left_w_rv64 = {PSLLI_W, PSSLAI_W}

enum p_ps = {PSABS_B, PSABS_H, PSEXTB_H, PSEXTB_W, PSEXTH_W}

enum p_add_shift = {PSLL_B_B0, PADD_B_B0, PSLL_H_H0, PADD_H_H0, PSSHA_H_H0, PSSHAR_H_H0, PSLL_W_W0, PADD_W_W0, PSSHA_W_W0, PSSHAR_W_W0, SSHA, SSHAR, SHA, SHAR}

enum p_shift_sat_b = {PSRLI_B, PSRAI_B}

enum p_shift_sat_h = {PSRLI_H, PUSATI_H, PSRAI_H, PSRARI_H, PSATI_H}

enum p_shift_sat_w = {PSRLI_W, PUSATI_W, PSRAI_W, PSRARI_W, PSATI_W}

enum p_shift_sat = {USATI, SRARI, SATI}

enum p_shift_sum = {PSRL_B_B0, PSRA_B_B0, PSRL_H_H0, PSRA_H_H0, PSRL_W_W0, PSRA_W_W0, PREDSUM_H, PREDSUMU_H, PREDSUM_W, PREDSUMU_W}

enum p_elementary_b = {PADD_B, PSADD_B, PAADD_B, PSADDU_B, PAADDU_B, PSUB_B, PDIF_B, PSSUB_B, PASUB_B, PDIFU_B, PSSUBU_B, PASUBU_B}

enum p_elementary_h = {PADD_H, PSADD_H, PAADD_H, PSADDU_H, PAADDU_H, PSUB_H, PDIF_H, PSSUB_H, PASUB_H, PDIFU_H, PSSUBU_H, PASUBU_H}

enum p_elementary_w = {PADD_W, PSADD_W, PAADD_W, PSADDU_W, PAADDU_W, PSUB_W, PSSUB_W, PASUB_W, PSSUBU_W, PASUBU_W}

enum p_elementary = {SADD, AADD, SADDU, AADDU, SSUB, ASUB, SSUBU, ASUBU}

enum p_p11 = {MVM, MVMN, MERGE, SRX, PDIFSUMU_B, PDIFSUMAU_B, PMUL_H_BEO, PMULU_H_BEO, MUL_H01, MACC_H01, MULU_H01, MACCU_H01, PMUL_W_HEO, PMACC_W_HEO, PMULU_W_HEO, PMACCU_W_HEO, MUL_W01, MACC_W01, MULU_W01, MACCU_W01}

enum p_sh1add = {PSH1ADD_H, PSSH1SADD_H, SSH1SADD, PSH1ADD_W, PSSH1SADD_W}

enum p_zip = {UNZIP8P, UNZIP16P, UNZIP8HP, UNZIP16HP, ZIP8P, ZIP16P, ZIP8HP, ZIP16HP}

enum p_mul_b = {PMUL_H_BEE, PMUL_H_BOO, PMULU_H_BEE, PMULU_H_BOO, PMULSU_H_BEE, PMULSU_H_BOO}

enum p_mul_h = {PMUL_W_HEE, PMUL_W_HOO, PMULU_W_HEE, PMULU_W_HOO, PMULSU_W_HEE, PMULSU_W_HOO,
                PMACC_W_HEE, PMACC_W_HOO, PMACCU_W_HEE, PMACCU_W_HOO, PMACCSU_W_HEE, PMACCSU_W_HOO,
                PMQRACC_W_HEO, PMQACC_W_HEO,
                MUL_H00, MUL_H11, MULU_H00, MULU_H11, MULSU_H00, MULSU_H11,
                MACC_H00, MACC_H11, MACCU_H00, MACCU_H11, MACCSU_H00, MACCSU_H11,
                MQRACC_H01, MQACC_H01}

enum p_mul_w = {MUL_W00, MUL_W11, MULU_W00, MULU_W11, MULSU_W00, MULSU_W11,
                MACC_W00, MACC_W11, MACCU_W00, MACCU_W11, MACCSU_W00, MACCSU_W11,
                MQACC_W01, MQRACC_W01}

enum p_pack_h = {PPACK_H, PPACKBT_H, PPACKTB_H, PPACKT_H}

enum p_pack_w = {PPACK_W, PPACKBT_W, PPACKTB_W, PPACKT_W}

enum p_pack = {PACKBT, PACKTB, PACKT}

enum p_mul2horizon_h = {PM2ADD_H, PM2ADDA_H, PM2ADD_HX, PM2ADDA_HX, PM2ADDU_H, PM2ADDAU_H, PM2ADDSU_H, PM2ADDASU_H,
                        PM2SADD_H, PM2SADD_HX, PMQ2ADD_H, PMQ2ADDA_H, PMQR2ADD_H, PMQR2ADDA_H,
                        PM2SUB_H, PM2SUBA_H, PM2SUB_HX, PM2SUBA_HX}

enum p_mul2horizon_w = {PM2ADD_W, PM2ADDA_W, PM2ADD_WX, PM2ADDA_WX, PM2ADDU_W, PM2ADDAU_W, PM2ADDSU_W, PM2ADDASU_W,
                        PMQ2ADD_W, PMQ2ADDA_W, PMQR2ADD_W, PMQR2ADDA_W,
                        PM2SUB_W, PM2SUBA_W, PM2SUB_WX, PM2SUBA_WX}

enum p_mul4horizon_b = {PM4ADD_B, PM4ADDA_B, PM4ADDU_B, PM4ADDAU_B, PM4ADDSU_B, PM4ADDASU_B}

enum p_mul4horizon_h = {PM4ADD_H, PM4ADDA_H, PM4ADDU_H, PM4ADDAU_H, PM4ADDSU_H, PM4ADDASU_H}

enum p_addsub_h = {PAS_HX, PSA_HX, PSAS_HX, PSSA_HX, PAAS_HX, PASA_HX}

enum p_addsub_w = {PAS_WX, PSA_WX, PSAS_WX, PSSA_WX, PAAS_WX, PASA_WX}

enum p_comparison_b = {PMSEQ_B, PMSLT_B, PMSLTU_B, PMIN_B, PMINU_B, PMAX_B, PMAXU_B}

enum p_comparison_h = {PMSEQ_H, PMSLT_H, PMSLTU_H, PMIN_H, PMINU_H, PMAX_H, PMAXU_H}

enum p_comparison_w = {PMSEQ_W, PMSLT_W, PMSLTU_W, PMIN_W, PMINU_W, PMAX_W, PMAXU_W}

// Get the bit encoding of word_width.
mapping size_enc : word_width <-> bits(2) = {
  BYTE   <-> 0b00,
  HALF   <-> 0b01,
  WORD   <-> 0b10,
  DOUBLE <-> 0b11
}

mapping size_mnemonic : word_width <-> string = {
  BYTE   <-> "b",
  HALF   <-> "h",
  WORD   <-> "w",
  DOUBLE <-> "d"
}

mapping size_bytes : word_width <-> {1, 2, 4, 8} = {
  BYTE   <-> 1,
  HALF   <-> 2,
  WORD   <-> 4,
  DOUBLE <-> 8,
}

struct mul_op = {
  high       : bool,
  signed_rs1 : bool,
  signed_rs2 : bool
}

/*!
 * Raise an internal error reporting that width w is invalid for access kind, k,
 * and current xlen. The file name and line number should be passed in as the
 * first two arguments using the __FILE__ and __LINE__ built-in macros.
 * This is mainly used to supress Sail warnings about incomplete matches and
 * should be unreachable. See https://github.com/riscv/sail-riscv/issues/194
 * and https://github.com/riscv/sail-riscv/pull/197 .
 */
val report_invalid_width : forall ('a : Type). (string, int, word_width, string) -> 'a
function report_invalid_width(f , l, w, k) -> 'a = {
  internal_error(f, l, "Invalid width, " ^ size_mnemonic(w) ^ ", for " ^ k ^
     " with xlen=" ^ dec_str(sizeof(xlen)))
}
