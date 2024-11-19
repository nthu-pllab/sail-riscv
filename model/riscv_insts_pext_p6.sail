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

// TODO: Figure out PLI and PLUI and implement them.
