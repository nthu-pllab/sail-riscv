union clause ast = PEXT_SHIFT_LEFT_B : (bits(3), regidx, regidx, pshift_left_b)

mapping clause encdec = PEXT_SHIFT_LEFT_B(imm3, rs1, rd, PSLLI_B) <->
  0b1 @ 0b000 @ 0b0 @ 0b0001 @ imm3 @ rs1 @ 0b010 @ rd @ 0b0011011

function clause execute (PEXT_SHIFT_LEFT_B(imm3, rs1, rd, op)) = {
  match op {
    PSLLI_B => {
      let rs1_val = X(rs1);
      let sa : bits(8) = EXTZ(imm3);
      var result : xlenbits = zeros();
      foreach (i from 0 to (sizeof(xlen) - 8) by 8) {
        let rs1_byte = slice(rs1_val, i, 8);
        result[(i+7)..i] = shift_left_logic(rs1_byte, sa)
      };
      X(rd) = result;
    }
  };
  RETIRE_SUCCESS
}

mapping p_shift_b_mapping : pshift_left_b <-> string = {
  PSLLI_B <-> "pslli.b"
}

mapping clause assembly = PEXT_SHIFT_LEFT_B(imm3, rs1, rd, p_inst)
  <-> p_shift_b_mapping(p_inst) ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ hex_bits_3(imm3)

/* ****************************************************************** */

union clause ast = PEXT_SHIFT_LEFT_W_RV64 : (bits(5), regidx, regidx, pshift_left_w_rv64)

mapping clause encdec = PEXT_SHIFT_LEFT_W_RV64(imm5, rs1, rd, PSLLI_W) if sizeof(xlen) == 64 <->
  0b1 @ 0b000 @ 0b0 @ 0b01 @ imm5 @ rs1 @ 0b010 @ rd @ 0b0011011 if sizeof(xlen) == 64
mapping clause encdec = PEXT_SHIFT_LEFT_W_RV64(imm5, rs1, rd, PSSLAI_W) if sizeof(xlen) == 64 <->
  0b1 @ 0b101 @ 0b0 @ 0b01 @ imm5 @ rs1 @ 0b010 @ rd @ 0b0011011 if sizeof(xlen) == 64

function clause execute (PEXT_SHIFT_LEFT_W_RV64(imm5, rs1, rd, op)) = {
  let rs1_val = X(rs1);
  let sa : bits(8) = EXTZ(imm5);
  var result : xlenbits = zeros();
  foreach (i from 0 to (sizeof(xlen) - 32) by 32) {
    let rs1_word = slice(rs1_val, i, 32);
    result[(i+31)..i] = match op {
      PSLLI_W => shift_left_logic(rs1_word, sa),
      PSSLAI_W => sat_shift_left_arith(rs1_word, sa)
    };
  };
  X(rd) = result;
  RETIRE_SUCCESS
}

mapping p_shift_w_rv64_mapping : pshift_left_w_rv64 <-> string = {
  PSLLI_W <-> "pslli.w",
  PSSLAI_W <-> "psslai.w"
}

mapping clause assembly = PEXT_SHIFT_LEFT_W_RV64(imm5, rs1, rd, p_inst)
  <-> p_shift_w_rv64_mapping(p_inst) ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ hex_bits_5(imm5)

/* ****************************************************************** */

union clause ast = PEXT_SHIFT_LEFT_W_RV32 : (bits(5), regidx, regidx, pshift_left_w_rv32)

mapping clause encdec = PEXT_SHIFT_LEFT_W_RV32(imm5, rs1, rd, SSLAI) if sizeof(xlen) == 32 <->
  0b1 @ 0b101 @ 0b0 @ 0b01 @ imm5 @ rs1 @ 0b010 @ rd @ 0b0011011 if sizeof(xlen) == 32

function clause execute (PEXT_SHIFT_LEFT_W_RV32(imm5, rs1, rd, op)) = {
  let rs1_val = X(rs1);
  let sa : bits(8) = EXTZ(imm5);
  X(rd) = sat_shift_left_arith(rs1_val, sa);
  RETIRE_SUCCESS
}

mapping p_shift_w_rv32_mapping : pshift_left_w_rv32 <-> string = {
  SSLAI <-> "sslai"
}

mapping clause assembly = PEXT_SHIFT_LEFT_W_RV32(imm5, rs1, rd, p_inst)
  <-> p_shift_w_rv32_mapping(p_inst) ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ hex_bits_5(imm5)

/* ****************************************************************** */

union clause ast = PEXT_SHIFT_LEFT_H : (bits(4), regidx, regidx, pshift_left_h)

mapping clause encdec = PEXT_SHIFT_LEFT_H(imm4, rs1, rd, PSLLI_H) <->
  0b1 @ 0b000 @ 0b0 @ 0b001 @ imm4 @ rs1 @ 0b010 @ rd @ 0b0011011
mapping clause encdec = PEXT_SHIFT_LEFT_H(imm4, rs1, rd, PSSLAI_H) <->
  0b1 @ 0b101 @ 0b0 @ 0b001 @ imm4 @ rs1 @ 0b010 @ rd @ 0b0011011

function clause execute (PEXT_SHIFT_LEFT_H(imm4, rs1, rd, op)) = {
  let rs1_val = X(rs1);
  let sa : bits(8) = EXTZ(imm4);
  var result : xlenbits = zeros();
  foreach (i from 0 to (sizeof(xlen) - 16) by 16) {
    let rs1_halfword = slice(rs1_val, i, 16);
    result[(i+15)..i] = match op {
      PSLLI_H => shift_left_logic(rs1_halfword, sa),
      PSSLAI_H => sat_shift_left_arith(rs1_halfword, sa)
    };
  };
  X(rd) = result;
  RETIRE_SUCCESS
}

mapping p_shift_h_mapping : pshift_left_h <-> string = {
  PSLLI_H <-> "pslli.h",
  PSSLAI_H <-> "psslai.h"
}

mapping clause assembly = PEXT_SHIFT_LEFT_H(imm4, rs1, rd, p_inst)
  <-> p_shift_h_mapping(p_inst) ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ hex_bits_4(imm4)

/* ****************************************************************** */

union clause ast = PEXT_LOAD_IMM_H : (bits(10), regidx, p_load_imm_h)

mapping clause encdec = PEXT_LOAD_IMM_H(imm10, rd, PLI_H) <->
  0b10110 @ 0b00 @ imm10 @ 0b010 @ rd @ 0b0011011

function clause execute (PEXT_LOAD_IMM_H(imm10, rd, op)) = {
  var result : xlenbits = zeros();
  foreach (i from 0 to (sizeof(xlen) - 16) by 16) {
    result[(i+15)..i] = match op {
      PLI_H => if (imm10 & 0b0000000001) == 0b0000000001 then sail_ones(7) @ imm10[9..1] else sail_zeros(7) @ imm10[9..1]
    };
  };
  X(rd) = result;
  RETIRE_SUCCESS
}

mapping p_load_imm_h_mapping : p_load_imm_h <-> string = {
  PLI_H <-> "pli.h"
}

mapping clause assembly = PEXT_LOAD_IMM_H(imm10, rd, p_inst)
  <-> p_load_imm_h_mapping(p_inst) ^ spc() ^ reg_name(rd) ^ sep() ^ hex_bits_10(imm10[8..0] @ imm10[9])

/* ****************************************************************** */

union clause ast = PEXT_LOAD_IMM_W : (bits(10), regidx, p_load_imm_w)

mapping clause encdec = PEXT_LOAD_IMM_W(imm10, rd, PLI_W) if sizeof(xlen) == 64 <->
  0b10110 @ 0b01 @ imm10 @ 0b010 @ rd @ 0b0011011 if sizeof(xlen) == 64

function clause execute (PEXT_LOAD_IMM_W(imm10, rd, op)) = {
  var result : xlenbits = zeros();
  foreach (i from 0 to (sizeof(xlen) - 32) by 32) {
    result[(i+31)..i] = match op {
      PLI_W => if (imm10 & 0b0000000001) == 0b0000000001 then sail_ones(23) @ imm10[9..1] else sail_zeros(23) @ imm10[9..1]
    };
  };
  X(rd) = result;
  RETIRE_SUCCESS
}

mapping p_load_imm_w_mapping : p_load_imm_w <-> string = {
  PLI_W <-> "pli.w"
}

mapping clause assembly = PEXT_LOAD_IMM_W(imm10, rd, p_inst)
  <-> p_load_imm_w_mapping(p_inst) ^ spc() ^ reg_name(rd) ^ sep() ^ hex_bits_10(imm10[8..0] @ imm10[9])

/* ****************************************************************** */

union clause ast = PEXT_LOAD_IMM_B : (bits(8), regidx, p_load_imm_b)

mapping clause encdec = PEXT_LOAD_IMM_B(imm8, rd, PLI_B) <->
  0b10110 @ 0b100 @ imm8 @ 0b0010 @ rd @ 0b0011011

function clause execute (PEXT_LOAD_IMM_B(imm8, rd, op)) = {
  var result : xlenbits = zeros();
  foreach (i from 0 to (sizeof(xlen) - 8) by 8) {
    result[(i+7)..i] = match op {
      PLI_B => imm8
    };
  };
  X(rd) = result;
  RETIRE_SUCCESS
}

mapping p_load_imm_b_mapping : p_load_imm_b <-> string = {
  PLI_B <-> "pli.b"
}

mapping clause assembly = PEXT_LOAD_IMM_B(imm8, rd, p_inst)
  <-> p_load_imm_b_mapping(p_inst) ^ spc() ^ reg_name(rd) ^ sep() ^ hex_bits_8(imm8)
