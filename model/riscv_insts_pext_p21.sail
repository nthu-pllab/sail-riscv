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

mapping clause encdec = PEXT_PS_RV32(rs1p, rdp, PSEXTB_DH) <->
  0b01100 @ 0b00 @ 0b00100 @ rs1p @ 0b0110 @ rdp @ 0b00011011
mapping clause encdec = PEXT_PS_RV32(rs1p, rdp, PSEXTB_DW) <->
  0b01100 @ 0b01 @ 0b00100 @ rs1p @ 0b0110 @ rdp @ 0b00011011
mapping clause encdec = PEXT_PS_RV32(rs1p, rdp, PSEXTH_DW) <->
  0b01100 @ 0b01 @ 0b00101 @ rs1p @ 0b0110 @ rdp @ 0b00011011
mapping clause encdec = PEXT_PS_RV32(rs1p, rdp, PSABS_DH) <->
  0b01100 @ 0b00 @ 0b00111 @ rs1p @ 0b0110 @ rdp @ 0b00011011
mapping clause encdec = PEXT_PS_RV32(rs1p, rdp, PSABS_DB) <->
  0b01100 @ 0b10 @ 0b00111 @ rs1p @ 0b0110 @ rdp @ 0b00011011

function clause execute (PEXT_PS_RV32(rs1p, rdp, op)) = {
  let rs1_val = X(rs1p @ 0b1) @ X(rs1p @ 0b0);
  var result : bits(64) = zeros();
  match op {
    PSEXTB_DH => {
      foreach (i from 0 to (64 - 16) by 16) {
        result[(i+15)..i] = EXTS(rs1_val[(i+7)..i])
      };
    },
    PSEXTB_DW => {
      foreach (i from 0 to (64 - 32) by 32) {
        result[(i+31)..i] = EXTS(rs1_val[(i+7)..i])
      };
    },
    PSEXTH_DW => {
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
  PSEXTB_DH <-> "psextb.dh",
  PSEXTB_DW <-> "psextb.dw",
  PSEXTH_DW <-> "psexth.dw",
  PSABS_DH <-> "psabs.dh",
  PSABS_DB <-> "psabs.dw"
}

mapping clause assembly = PEXT_PS_RV32(rs1p, rdp, p_inst)
  <-> p_ps_rv32_mapping(p_inst) ^ spc() ^ preg_name(rdp) ^ sep() ^ preg_name(rs1p)

/* ****************************************************************** */

union clause ast = PEXT_ADD_SHIFT_RV32 : (pregidx, regidx, pregidx, p_add_shift_rv32)

mapping clause encdec = PEXT_ADD_SHIFT_RV32(rs1p, rs2, rdp, PSLL_DH_H0) <->
  0b0 @ 0b000 @ 0b1 @ 0b00 @ rs2 @ rs1p @ 0b0110 @ rdp @ 0b00011011
mapping clause encdec = PEXT_ADD_SHIFT_RV32(rs1p, rs2, rdp, PADD_DH_H0) <->
  0b0 @ 0b001 @ 0b1 @ 0b00 @ rs2 @ rs1p @ 0b0110 @ rdp @ 0b00011011
mapping clause encdec = PEXT_ADD_SHIFT_RV32(rs1p, rs2, rdp, PSSHA_DH_H0) <->
  0b0 @ 0b110 @ 0b1 @ 0b00 @ rs2 @ rs1p @ 0b0110 @ rdp @ 0b00011011
mapping clause encdec = PEXT_ADD_SHIFT_RV32(rs1p, rs2, rdp, PSSHAR_DH_H0) <->
  0b0 @ 0b111 @ 0b1 @ 0b00 @ rs2 @ rs1p @ 0b0110 @ rdp @ 0b00011011
mapping clause encdec = PEXT_ADD_SHIFT_RV32(rs1p, rs2, rdp, PSLL_DW_W) <->
  0b0 @ 0b000 @ 0b1 @ 0b01 @ rs2 @ rs1p @ 0b0110 @ rdp @ 0b00011011
mapping clause encdec = PEXT_ADD_SHIFT_RV32(rs1p, rs2, rdp, PADD_DW_W) <->
  0b0 @ 0b001 @ 0b1 @ 0b01 @ rs2 @ rs1p @ 0b0110 @ rdp @ 0b00011011
mapping clause encdec = PEXT_ADD_SHIFT_RV32(rs1p, rs2, rdp, PSSHA_DW_W) <->
  0b0 @ 0b110 @ 0b1 @ 0b01 @ rs2 @ rs1p @ 0b0110 @ rdp @ 0b00011011
mapping clause encdec = PEXT_ADD_SHIFT_RV32(rs1p, rs2, rdp, PSSHAR_DW_W) <->
  0b0 @ 0b111 @ 0b1 @ 0b01 @ rs2 @ rs1p @ 0b0110 @ rdp @ 0b00011011
mapping clause encdec = PEXT_ADD_SHIFT_RV32(rs1p, rs2, rdp, PSLL_DB_B0) <->
  0b0 @ 0b000 @ 0b1 @ 0b10 @ rs2 @ rs1p @ 0b0110 @ rdp @ 0b00011011
mapping clause encdec = PEXT_ADD_SHIFT_RV32(rs1p, rs2, rdp, PADD_DB_B0) <->
  0b0 @ 0b001 @ 0b1 @ 0b10 @ rs2 @ rs1p @ 0b0110 @ rdp @ 0b00011011

function clause execute (PEXT_ADD_SHIFT_RV32(rs1p, rs2, rdp, op)) = {
  let rs1_val = X(rs1p @ 0b1) @ X(rs1p @ 0b0);
  let rs2_val = X(rs2);
  var result : bits(64) = zeros();
  match op {
    PSLL_DH_H0 => {
      foreach (i from 0 to (64 - 16) by 16) {
        result[(i+15)..i] = shift_left_logic(rs1_val[(i+15)..i], rs2_val[7..0])
      };
    },
    PADD_DH_H0 => {
      foreach (i from 0 to (64 - 16) by 16) {
        result[(i+15)..i] = rs1_val[(i+15)..i] + rs2_val[15..0]
      };
    },
    PSSHA_DH_H0 => {
      foreach (i from 0 to (64 - 16) by 16) {
        result[(i+15)..i] = ssha(rs1_val[(i+15)..i], rs2_val[7..0])
      };
    },
    PSSHAR_DH_H0 => {
      foreach (i from 0 to (64 - 16) by 16) {
        result[(i+15)..i] = sshar(rs1_val[(i+15)..i], rs2_val[7..0])
      };
    },
    PSLL_DW_W => {
      foreach (i from 0 to (64 - 32) by 32) {
        result[(i+31)..i] = shift_left_logic(rs1_val[(i+31)..i], rs2_val[7..0])
      };
    },
    PADD_DW_W => {
      foreach (i from 0 to (64 - 32) by 32) {
        result[(i+31)..i] = rs1_val[(i+31)..i] + rs2_val[31..0]
      };
    },
    PSSHA_DW_W => {
      foreach (i from 0 to (64 - 32) by 32) {
        result[(i+31)..i] = ssha(rs1_val[(i+31)..i], rs2_val[7..0])
      };
    },
    PSSHAR_DW_W => {
      foreach (i from 0 to (64 - 32) by 32) {
        result[(i+31)..i] = sshar(rs1_val[(i+31)..i], rs2_val[7..0])
      };
    },
    PSLL_DB_B0 => {
      foreach (i from 0 to (64 - 8) by 8) {
        result[(i+7)..i] = shift_left_logic(rs1_val[(i+7)..i], rs2_val[7..0])
      };
    },
    PADD_DB_B0 => {
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
  PSLL_DH_H0 <-> "psll.dh.h0",
  PADD_DH_H0 <-> "padd.dh.h0",
  PSSHA_DH_H0 <-> "pssha.dh.h0",
  PSSHAR_DH_H0 <-> "psshar.dh.h0",
  PSLL_DW_W <-> "psll.dw.w",
  PADD_DW_W <-> "padd.dw.w",
  PSSHA_DW_W <-> "pssha.dw.w",
  PSSHAR_DW_W <-> "psshar.dw.w",
  PSLL_DB_B0 <-> "psll.db.b0",
  PADD_DB_B0 <-> "padd.db.b0"
}

mapping clause assembly = PEXT_ADD_SHIFT_RV32(rs1p, rs2, rdp, p_inst)
  <-> p_add_shift_rv32_mapping(p_inst) ^ spc() ^ preg_name(rdp) ^ sep() ^ preg_name(rs1p) ^ sep() ^ reg_name(rs2)
