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
type pregidx  = bits(4)   /* identifiers in RVP instructions */
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

enum p_load_imm_h = {PLI_H}

enum p_load_imm_w = {PLI_W}

enum p_load_imm_b = {PLI_B}

enum p_load_upper_imm_h = {PLUI_H}

enum p_load_upper_imm_w = {PLUI_W}

enum p_ps = {PSABS_B, PSABS_H, PSEXT_H_B, PSEXT_W_B, PSEXT_W_H}

enum p_add_shift = {PSLL_BS, PADD_BS, PSLL_HS, PADD_HS, PSSHA_HS, PSSHAR_HS, PSLL_WS, PADD_WS, PSSHA_WS, PSSHAR_WS, SSHA, SSHAR, SHA, SHAR}

enum p_shift_sat_b = {PSRLI_B, PSRAI_B}

enum p_shift_sat_h = {PSRLI_H, PUSATI_H, PSRAI_H, PSRARI_H, PSATI_H}

enum p_shift_sat_w = {PSRLI_W, PUSATI_W, PSRAI_W, PSRARI_W, PSATI_W}

enum p_shift_sat = {USATI, SRARI, SATI}

enum p_shift_sum = {PSRL_BS, PSRA_BS, PSRL_HS, PSRA_HS, PSRL_WS, PSRA_WS, PREDSUM_HS, PREDSUMU_HS, PREDSUM_WS, PREDSUMU_WS}

enum p_elementary_b = {PADD_B, PSADD_B, PAADD_B, PSADDU_B, PAADDU_B, PSUB_B, PDIF_B, PSSUB_B, PASUB_B, PDIFU_B, PSSUBU_B, PASUBU_B}

enum p_elementary_h = {PADD_H, PSADD_H, PAADD_H, PSADDU_H, PAADDU_H, PSUB_H, PDIF_H, PSSUB_H, PASUB_H, PDIFU_H, PSSUBU_H, PASUBU_H}

enum p_elementary_w = {PADD_W, PSADD_W, PAADD_W, PSADDU_W, PAADDU_W, PSUB_W, PSSUB_W, PASUB_W, PSSUBU_W, PASUBU_W}

enum p_elementary = {SADD, AADD, SADDU, AADDU, SSUB, ASUB, SSUBU, ASUBU}

enum p_p11 = {MVM, MVMN, MERGE, SRX, PDIFSUMU_B, PDIFSUMAU_B, PMUL_H_B01, PMULU_H_B01, MUL_H01, MACC_H01, MULU_H01, MACCU_H01, PMUL_W_H01, PMACC_W_H01, PMULU_W_H01, PMACCU_W_H01, MUL_W01, MACC_W01, MULU_W01, MACCU_W01}

enum p_sh1add = {PSH1ADD_H, PSSH1SADD_H, SSH1SADD, PSH1ADD_W, PSSH1SADD_W}

enum p_zip = {UNZIP8P, UNZIP16P, UNZIP8HP, UNZIP16HP, ZIP8P, ZIP16P, ZIP8HP, ZIP16HP}

enum p_mul_b = {PMUL_H_B00, PMUL_H_B11, PMULU_H_B00, PMULU_H_B11, PMULSU_H_B00, PMULSU_H_B11}

enum p_mul_h = {PMUL_W_H00, PMUL_W_H11, PMULU_W_H00, PMULU_W_H11, PMULSU_W_H00, PMULSU_W_H11,
                PMACC_W_H00, PMACC_W_H11, PMACCU_W_H00, PMACCU_W_H11, PMACCSU_W_H00, PMACCSU_W_H11,
                PMQRACC_W_H01, PMQACC_W_H01,
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

enum p_mul = {PMULH_H, PMHACC_H, PMULHU_H, PMHACCU_H,
              PMULH_H_B0, PMHACC_H_B0, PMULH_H_B1, PMHACC_H_B1,
              PMULHSU_H, PMHACCSU_H, PMULQ_H,
              MQACC_H00, MQACC_H11, PMQACC_W_H00, PMQACC_W_H11,
              PMULHR_H, PMHRACC_H, PMULHRU_H, PMHRACCU_H,
              PMULHSU_H_B0, PMHACCSU_H_B0, PMULHSU_H_B1, PMHACCSU_H_B1,
              PMULHRSU_H, PMHRACCSU_H, PMULQR_H,
              MQRACC_H00, MQRACC_H11, PMQRACC_W_H00, PMQRACC_W_H11,
              MHACC, MHACCU, MULH_H0, MHACC_H0, MULH_H1, MHACC_H1, MHACCSU, MULQ,
              PMULH_W, PMHACC_W, PMULHU_W, PMHACCU_W, PMULH_W_H0, PMHACC_W_H0, PMULH_W_H1, PMHACC_W_H1, PMULHSU_W, PMHACCSU_W, PMULQ_W, MQACC_W00, MQACC_W11,
              MULHR, MHRACC, MULHRU, MHRACCU, MULHSU_H0, MHACCSU_H0, MULHSU_H1, MHACCSU_H1, MULHRSU, MHRACCSU, MULQR,
              PMULHR_W, PMHRACC_W, PMULHRU_W, PMHRACCU_W, PMULHSU_W_H0, PMHACCSU_W_H0, PMULHSU_W_H1, PMHACCSU_W_H1, PMULHRSU_W, PMHRACCSU_W, PMULQR_W, MQRACC_W00, MQRACC_W11}

enum p_widening_shift_left_imm_b = {PWSLLI_B, PWSLAI_B}

enum p_widening_shift_left_imm_h = {PWSLLI_H, PWSLAI_H}

enum p_widening_shift_left_imm_w = {WSLLI, WSLAI}

enum p_load_imm_h_rv32 = {PLI_DH}

enum p_load_imm_b_rv32 = {PLI_DB}

enum p_load_upper_imm_h_rv32 = {PLUI_DH}

enum p_widening_shift_left_b = {PWSLL_BS, PWSLA_BS}

enum p_widening_shift_left_h = {PWSLL_HS, PWSLA_HS}

enum p_widening_shift_left_w = {WSLL, WSLA}

enum p_widening_zip = {WZIP8P, WZIP16P}

enum p_widening_elementary_b = {PWADD_B, PWADDA_B, PWADDU_B, PWADDAU_B, PWMUL_B, PWMULU_B, PWSUB_B, PWSUBA_B, PWSUBU_B, PWSUBAU_B, PWMULSU_B}

enum p_widening_elementary_h = {PWADD_H, PWADDA_H, PWADDU_H, PWADDAU_H, PWMUL_H, PWMACC_H, PWMULU_H, PWMACCU_H, PWSUB_H, PWSUBA_H, PWSUBU_H, PWSUBAU_H, PWMULSU_H, PWMACCSU_H}

enum p_widening_elementary_w = {WADD, WADDA, WADDU, WADDAU, WMUL, WMACC, WMULU, WMACCU, WSUB, WSUBA, WSUBU, WSUBAU, WMULSU, WMACCSU}

enum p_widening_mul2horizon_h = {PM2WADD_H, PM2WADDA_H, PM2WADD_HX, PM2WADDA_HX,
                                 PM2WADDU_H, PM2WADDAU_H, PM2WADDSU_H, PM2WADDASU_H,
                                 PM2WSUB_H, PM2WSUBA_H, PM2WSUB_HX, PM2WSUBA_HX}

enum p_widening_mul_h = {PMQWACC_H, PMQRWACC_H}

enum p_widening_mul_w = {PMQWACC, PMQRWACC}

enum p_sum_rv32 = {PREDSUM_DHS, PREDSUMU_DHS}

enum p_narrowing_shift_clip_imm_b = {PNSRLI_B, PNCLIPIU_B, PNCLIPRIU_B, PNSRAI_B, PNSRARI_B, PNCLIPI_B, PNCLIPRI_B}

enum p_narrowing_shift_clip_imm_h = {PNSRLI_H, PNCLIPIU_H, PNCLIPRIU_H, PNSRAI_H, PNSRARI_H, PNCLIPI_H, PNCLIPRI_H}

enum p_narrowing_shift_clip_imm_w = {NSRLI, NCLIPIU, NCLIPRIU, NSRAI, NSRARI, NCLIPI, NCLIPRI}

enum p_narrowing_shift_clip_b = {PNSRL_BS, PNCLIPU_BS, PNCLIPRU_BS, PNSRA_BS, PNSRAR_BS, PNCLIP_BS, PNCLIPR_BS}

enum p_narrowing_shift_clip_h = {PNSRL_HS, PNCLIPU_HS, PNCLIPRU_HS, PNSRA_HS, PNSRAR_HS, PNCLIP_HS, PNCLIPR_HS}

enum p_narrowing_shift_clip_w = {NSRL, NCLIPU, NCLIPRU, NSRA, NSRAR, NCLIP, NCLIPR}

enum p_shift_sat_imm_b_rv32 = {PSLLI_DB}

enum p_shift_sat_imm_h_rv32 = {PSLLI_DH, PSSLAI_DH}

enum p_shift_sat_imm_w_rv32 = {PSLLI_DW, PSSLAI_DW}

enum p_ps_rv32 = {PSEXT_DH_B, PSEXT_DW_B, PSEXT_DW_H, PSABS_DH, PSABS_DB}

enum p_add_shift_rv32 = {PSLL_DHS, PADD_DHS, PSSHA_DHS, PSSHAR_DHS, PSLL_DWS, PADD_DWS, PSSHA_DWS, PSSHAR_DWS, PSLL_DBS, PADD_DBS}

enum p_shift_sat_b_rv32 = {PSRLI_DB, PSRAI_DB}

enum p_shift_sat_h_rv32 = {PSRLI_DH, PUSATI_DH, PSRAI_DH, PSRARI_DH, PSATI_DH}

enum p_shift_sat_w_rv32 = {PSRLI_DW, PUSATI_DW, PSRAI_DW, PSRARI_DW, PSATI_DW}

enum p_shift_rv32 = {PSRL_DBS, PSRA_DBS, PSRL_DHS, PSRA_DHS, PSRL_DWS, PSRA_DWS}

enum p_elementary_b_rv32 = {PADD_DB, PSADD_DB, PAADD_DB, PSADDU_DB, PAADDU_DB, PSUB_DB, PDIF_DB, PSSUB_DB, PASUB_DB, PDIFU_DB, PSSUBU_DB, PASUBU_DB}

enum p_elementary_h_rv32 = {PADD_DH, PSADD_DH, PAADD_DH, PSADDU_DH, PAADDU_DH, PSUB_DH, PDIF_DH, PSSUB_DH, PASUB_DH, PDIFU_DH, PSSUBU_DH, PASUBU_DH}

enum p_elementary_w_rv32 = {PADD_DW, PSADD_DW, PAADD_DW, PSADDU_DW, PAADDU_DW, PSUB_DW, PSSUB_DW, PASUB_DW, PSSUBU_DW, PASUBU_DW}

enum p_elementary_rv32 = {ADDD, SUBD}

enum p_sh1add_rv32 = {PSH1ADD_DH, PSSH1SADD_DH, PSH1ADD_DW, PSSH1SADD_DW}

enum p_pack_h_rv32 = {PPACK_DH, PPACKBT_DH, PPACKTB_DH, PPACKT_DH}

enum p_pack_w_rv32 = {PPACK_DW, PPACKBT_DW, PPACKTB_DW, PPACKT_DW}

enum p_addsub_h_rv32 = {PAS_DHX, PSA_DHX, PSAS_DHX, PSSA_DHX, PAAS_DHX, PASA_DHX}

enum p_comparison_b_rv32 = {PMSEQ_DB, PMSLT_DB, PMSLTU_DB, PMIN_DB, PMINU_DB, PMAX_DB, PMAXU_DB}

enum p_comparison_h_rv32 = {PMSEQ_DH, PMSLT_DH, PMSLTU_DH, PMIN_DH, PMINU_DH, PMAX_DH, PMAXU_DH}

enum p_comparison_w_rv32 = {PMSEQ_DW, PMSLT_DW, PMSLTU_DW, PMIN_DW, PMINU_DW, PMAX_DW, PMAXU_DW}

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
