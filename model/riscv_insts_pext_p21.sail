union clause ast = PEXT_SHIFT_SAT_IMM_B_RV32 : (bits(3), pregidx, pregidx, p_shift_sat_imm_b_rv32)

mapping clause encdec = PEXT_SHIFT_SAT_IMM_B_RV32(imm3, rs1p, rdp, PSLLI_DB) <->
  0b0 @ 0b000 @ 0b0 @ 0b0001 @ imm3 @ rs1p @ 0b0110 @ rdp @ 0b00011011

function clause execute (PEXT_SHIFT_SAT_IMM_B_RV32(imm3, rs1p, rdp, op)) = {
  let rs1_val = X(rs1p @ 0b1) @ X(rs1p @ 0b0);
  let sa : bits(8) = EXTZ(imm3);
  var result : bits(64) = zeros();
  foreach (i from 0 to (64 - 8) by 8) {
    result[(i+7)..i] = match op {
      PSLLI_DB => shift_left_logic(rs1_val[(i+7)..i], sa)
    };
  };
  X(rdp @ 0b1) = result[63..32];
  X(rdp @ 0b0) = result[31..0];
  RETIRE_SUCCESS
}

mapping p_shift_sat_imm_b_rv32_mapping : p_shift_sat_imm_b_rv32 <-> string = {
  PSLLI_DB <-> "pslli.db"
}

mapping clause assembly = PEXT_SHIFT_SAT_IMM_B_RV32(imm3, rs1p, rdp, p_inst)
  <-> p_shift_sat_imm_b_rv32_mapping(p_inst) ^ spc() ^ preg_name(rdp) ^ sep() ^ preg_name(rs1p) ^ sep() ^ hex_bits_3(imm3)

/* ****************************************************************** */

union clause ast = PEXT_SHIFT_SAT_IMM_H_RV32 : (bits(4), pregidx, pregidx, p_shift_sat_imm_h_rv32)

mapping clause encdec = PEXT_SHIFT_SAT_IMM_H_RV32(imm4, rs1p, rdp, PSLLI_DH) <->
  0b0 @ 0b000 @ 0b0 @ 0b001 @ imm4 @ rs1p @ 0b0110 @ rdp @ 0b00011011
mapping clause encdec = PEXT_SHIFT_SAT_IMM_H_RV32(imm4, rs1p, rdp, PSSLAI_DH) <->
  0b0 @ 0b101 @ 0b0 @ 0b001 @ imm4 @ rs1p @ 0b0110 @ rdp @ 0b00011011

function clause execute (PEXT_SHIFT_SAT_IMM_H_RV32(imm4, rs1p, rdp, op)) = {
  let rs1_val = X(rs1p @ 0b1) @ X(rs1p @ 0b0);
  let sa : bits(8) = EXTZ(imm4);
  var result : bits(64) = zeros();
  foreach (i from 0 to (64 - 16) by 16) {
    result[(i+15)..i] = match op {
      PSLLI_DH => shift_left_logic(rs1_val[(i+15)..i], sa),
      PSSLAI_DH => sat_shift_left_arith(rs1_val[(i+15)..i], sa)
    };
  };
  X(rdp @ 0b1) = result[63..32];
  X(rdp @ 0b0) = result[31..0];
  RETIRE_SUCCESS
}

mapping p_shift_sat_imm_h_rv32_mapping : p_shift_sat_imm_h_rv32 <-> string = {
  PSLLI_DH <-> "pslli.dh",
  PSSLAI_DH <-> "psslai.dh"
}

mapping clause assembly = PEXT_SHIFT_SAT_IMM_H_RV32(imm4, rs1p, rdp, p_inst)
  <-> p_shift_sat_imm_h_rv32_mapping(p_inst) ^ spc() ^ preg_name(rdp) ^ sep() ^ preg_name(rs1p) ^ sep() ^ hex_bits_4(imm4)

/* ****************************************************************** */

union clause ast = PEXT_SHIFT_SAT_IMM_W_RV32 : (bits(5), pregidx, pregidx, p_shift_sat_imm_w_rv32)

mapping clause encdec = PEXT_SHIFT_SAT_IMM_W_RV32(imm5, rs1p, rdp, PSLLI_DW) <->
  0b0 @ 0b000 @ 0b0 @ 0b01 @ imm5 @ rs1p @ 0b0110 @ rdp @ 0b00011011
mapping clause encdec = PEXT_SHIFT_SAT_IMM_W_RV32(imm5, rs1p, rdp, PSSLAI_DW) <->
  0b0 @ 0b101 @ 0b0 @ 0b01 @ imm5 @ rs1p @ 0b0110 @ rdp @ 0b00011011

function clause execute (PEXT_SHIFT_SAT_IMM_W_RV32(imm5, rs1p, rdp, op)) = {
  let rs1_val = X(rs1p @ 0b1) @ X(rs1p @ 0b0);
  let sa : bits(8) = EXTZ(imm5);
  var result : bits(64) = zeros();
  foreach (i from 0 to (64 - 32) by 32) {
    result[(i+31)..i] = match op {
      PSLLI_DW => shift_left_logic(rs1_val[(i+31)..i], sa),
      PSSLAI_DW => sat_shift_left_arith(rs1_val[(i+31)..i], sa)
    };
  };
  X(rdp @ 0b1) = result[63..32];
  X(rdp @ 0b0) = result[31..0];
  RETIRE_SUCCESS
}

mapping p_shift_sat_imm_w_rv32_mapping : p_shift_sat_imm_w_rv32 <-> string = {
  PSLLI_DW <-> "pslli.dw",
  PSSLAI_DW <-> "psslai.dw"
}

mapping clause assembly = PEXT_SHIFT_SAT_IMM_W_RV32(imm5, rs1p, rdp, p_inst)
  <-> p_shift_sat_imm_w_rv32_mapping(p_inst) ^ spc() ^ preg_name(rdp) ^ sep() ^ preg_name(rs1p) ^ sep() ^ hex_bits_5(imm5)

/* ****************************************************************** */

union clause ast = PEXT_PS_RV32 : (pregidx, pregidx, p_ps_rv32)

mapping clause encdec = PEXT_PS_RV32(rs1p, rdp, PSEXT_DH_B) <->
  0b01100 @ 0b00 @ 0b00100 @ rs1p @ 0b0110 @ rdp @ 0b00011011
mapping clause encdec = PEXT_PS_RV32(rs1p, rdp, PSEXT_DW_B) <->
  0b01100 @ 0b01 @ 0b00100 @ rs1p @ 0b0110 @ rdp @ 0b00011011
mapping clause encdec = PEXT_PS_RV32(rs1p, rdp, PSEXT_DW_H) <->
  0b01100 @ 0b01 @ 0b00101 @ rs1p @ 0b0110 @ rdp @ 0b00011011
mapping clause encdec = PEXT_PS_RV32(rs1p, rdp, PSABS_DH) <->
  0b01100 @ 0b00 @ 0b00111 @ rs1p @ 0b0110 @ rdp @ 0b00011011
mapping clause encdec = PEXT_PS_RV32(rs1p, rdp, PSABS_DB) <->
  0b01100 @ 0b10 @ 0b00111 @ rs1p @ 0b0110 @ rdp @ 0b00011011

function clause execute (PEXT_PS_RV32(rs1p, rdp, op)) = {
  let rs1_val = X(rs1p @ 0b1) @ X(rs1p @ 0b0);
  var result : bits(64) = zeros();
  match op {
    PSEXT_DH_B => {
      foreach (i from 0 to (64 - 16) by 16) {
        result[(i+15)..i] = EXTS(rs1_val[(i+7)..i])
      };
    },
    PSEXT_DW_B => {
      foreach (i from 0 to (64 - 32) by 32) {
        result[(i+31)..i] = EXTS(rs1_val[(i+7)..i])
      };
    },
    PSEXT_DW_H => {
      foreach (i from 0 to (64 - 32) by 32) {
        result[(i+31)..i] = EXTS(rs1_val[(i+15)..i])
      };
    },
    PSABS_DH => {
      foreach (i from 0 to (64 - 16) by 16) {
        result[(i+15)..i] = sabs(rs1_val[(i+15)..i])
      };
    },
    PSABS_DB => {
      foreach (i from 0 to (64 - 8) by 8) {
        result[(i+7)..i] = sabs(rs1_val[(i+7)..i])
      };
    }
  };
  X(rdp @ 0b1) = result[63..32];
  X(rdp @ 0b0) = result[31..0];
  RETIRE_SUCCESS
}

mapping p_ps_rv32_mapping : p_ps_rv32 <-> string = {
  PSEXT_DH_B <-> "psext.dh.b",
  PSEXT_DW_B <-> "psext.dw.b",
  PSEXT_DW_H <-> "psext.dw.h",
  PSABS_DH <-> "psabs.dh",
  PSABS_DB <-> "psabs.dw"
}

mapping clause assembly = PEXT_PS_RV32(rs1p, rdp, p_inst)
  <-> p_ps_rv32_mapping(p_inst) ^ spc() ^ preg_name(rdp) ^ sep() ^ preg_name(rs1p)

/* ****************************************************************** */

union clause ast = PEXT_ADD_SHIFT_RV32 : (pregidx, regidx, pregidx, p_add_shift_rv32)

mapping clause encdec = PEXT_ADD_SHIFT_RV32(rs1p, rs2, rdp, PSLL_DHS) <->
  0b0 @ 0b000 @ 0b1 @ 0b00 @ rs2 @ rs1p @ 0b0110 @ rdp @ 0b00011011
mapping clause encdec = PEXT_ADD_SHIFT_RV32(rs1p, rs2, rdp, PADD_DHS) <->
  0b0 @ 0b001 @ 0b1 @ 0b00 @ rs2 @ rs1p @ 0b0110 @ rdp @ 0b00011011
mapping clause encdec = PEXT_ADD_SHIFT_RV32(rs1p, rs2, rdp, PSSHA_DHS) <->
  0b0 @ 0b110 @ 0b1 @ 0b00 @ rs2 @ rs1p @ 0b0110 @ rdp @ 0b00011011
mapping clause encdec = PEXT_ADD_SHIFT_RV32(rs1p, rs2, rdp, PSSHAR_DHS) <->
  0b0 @ 0b111 @ 0b1 @ 0b00 @ rs2 @ rs1p @ 0b0110 @ rdp @ 0b00011011
mapping clause encdec = PEXT_ADD_SHIFT_RV32(rs1p, rs2, rdp, PSLL_DWS) <->
  0b0 @ 0b000 @ 0b1 @ 0b01 @ rs2 @ rs1p @ 0b0110 @ rdp @ 0b00011011
mapping clause encdec = PEXT_ADD_SHIFT_RV32(rs1p, rs2, rdp, PADD_DWS) <->
  0b0 @ 0b001 @ 0b1 @ 0b01 @ rs2 @ rs1p @ 0b0110 @ rdp @ 0b00011011
mapping clause encdec = PEXT_ADD_SHIFT_RV32(rs1p, rs2, rdp, PSSHA_DWS) <->
  0b0 @ 0b110 @ 0b1 @ 0b01 @ rs2 @ rs1p @ 0b0110 @ rdp @ 0b00011011
mapping clause encdec = PEXT_ADD_SHIFT_RV32(rs1p, rs2, rdp, PSSHAR_DWS) <->
  0b0 @ 0b111 @ 0b1 @ 0b01 @ rs2 @ rs1p @ 0b0110 @ rdp @ 0b00011011
mapping clause encdec = PEXT_ADD_SHIFT_RV32(rs1p, rs2, rdp, PSLL_DBS) <->
  0b0 @ 0b000 @ 0b1 @ 0b10 @ rs2 @ rs1p @ 0b0110 @ rdp @ 0b00011011
mapping clause encdec = PEXT_ADD_SHIFT_RV32(rs1p, rs2, rdp, PADD_DBS) <->
  0b0 @ 0b001 @ 0b1 @ 0b10 @ rs2 @ rs1p @ 0b0110 @ rdp @ 0b00011011

function clause execute (PEXT_ADD_SHIFT_RV32(rs1p, rs2, rdp, op)) = {
  let rs1_val = X(rs1p @ 0b1) @ X(rs1p @ 0b0);
  let rs2_val = X(rs2);
  var result : bits(64) = zeros();
  match op {
    PSLL_DHS => {
      foreach (i from 0 to (64 - 16) by 16) {
        result[(i+15)..i] = shift_left_logic(rs1_val[(i+15)..i], rs2_val[7..0])
      };
    },
    PADD_DHS => {
      foreach (i from 0 to (64 - 16) by 16) {
        result[(i+15)..i] = rs1_val[(i+15)..i] + rs2_val[15..0]
      };
    },
    PSSHA_DHS => {
      foreach (i from 0 to (64 - 16) by 16) {
        result[(i+15)..i] = ssha(rs1_val[(i+15)..i], rs2_val[7..0])
      };
    },
    PSSHAR_DHS => {
      foreach (i from 0 to (64 - 16) by 16) {
        result[(i+15)..i] = sshar(rs1_val[(i+15)..i], rs2_val[7..0])
      };
    },
    PSLL_DWS => {
      foreach (i from 0 to (64 - 32) by 32) {
        result[(i+31)..i] = shift_left_logic(rs1_val[(i+31)..i], rs2_val[7..0])
      };
    },
    PADD_DWS => {
      foreach (i from 0 to (64 - 32) by 32) {
        result[(i+31)..i] = rs1_val[(i+31)..i] + rs2_val[31..0]
      };
    },
    PSSHA_DWS => {
      foreach (i from 0 to (64 - 32) by 32) {
        result[(i+31)..i] = ssha(rs1_val[(i+31)..i], rs2_val[7..0])
      };
    },
    PSSHAR_DWS => {
      foreach (i from 0 to (64 - 32) by 32) {
        result[(i+31)..i] = sshar(rs1_val[(i+31)..i], rs2_val[7..0])
      };
    },
    PSLL_DBS => {
      foreach (i from 0 to (64 - 8) by 8) {
        result[(i+7)..i] = shift_left_logic(rs1_val[(i+7)..i], rs2_val[7..0])
      };
    },
    PADD_DBS => {
      foreach (i from 0 to (64 - 8) by 8) {
        result[(i+7)..i] = rs1_val[(i+7)..i] + rs2_val[7..0]
      };
    },
  };
  X(rdp @ 0b1) = result[63..32];
  X(rdp @ 0b0) = result[31..0];
  RETIRE_SUCCESS
}

mapping p_add_shift_rv32_mapping : p_add_shift_rv32 <-> string = {
  PSLL_DHS <-> "psll.dhs",
  PADD_DHS <-> "padd.dhs",
  PSSHA_DHS <-> "pssha.dhs",
  PSSHAR_DHS <-> "psshar.dhs",
  PSLL_DWS <-> "psll.dws",
  PADD_DWS <-> "padd.dws",
  PSSHA_DWS <-> "pssha.dws",
  PSSHAR_DWS <-> "psshar.dws",
  PSLL_DBS <-> "psll.dbs",
  PADD_DBS <-> "padd.dbs"
}

mapping clause assembly = PEXT_ADD_SHIFT_RV32(rs1p, rs2, rdp, p_inst)
  <-> p_add_shift_rv32_mapping(p_inst) ^ spc() ^ preg_name(rdp) ^ sep() ^ preg_name(rs1p) ^ sep() ^ reg_name(rs2)
