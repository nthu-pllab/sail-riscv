union clause ast = PEXT_SHIFT_SAT_B : (bits(3), regidx, regidx, p_shift_sat_b)

mapping clause encdec = PEXT_SHIFT_SAT_B(imm3, rs1, rd, PSRLI_B) <->
  0b1 @ 0b000 @ 0b0 @ 0b0001 @ imm3 @ rs1 @ 0b100 @ rd @ 0b0011011
mapping clause encdec = PEXT_SHIFT_SAT_B(imm3, rs1, rd, PSRAI_B) <->
  0b1 @ 0b000 @ 0b0 @ 0b0001 @ imm3 @ rs1 @ 0b100 @ rd @ 0b0011011

function clause execute (PEXT_SHIFT_SAT_B(imm3, rs1, rd, op)) = {
  let rs1_val = X(rs1);
  let sa : bits(8) = EXTZ(imm3);
  var result : xlenbits = zeros();
  foreach (i from 0 to (sizeof(xlen) - 8) by 8) {
    let rs1_byte = slice(rs1_val, i, 8);
    result[(i+7)..i] = match op {
      PSRLI_B => shift_right_logic(rs1_byte, sa),
      PSRAI_B => shift_right_arith(rs1_byte, sa)
    };
  };
  X(rd) = result;
  RETIRE_SUCCESS
}

mapping p_shift_sat_b_mapping : p_shift_sat_b <-> string = {
  PSRLI_B <-> "psrli.b",
  PSRAI_B <-> "psrai.b"
}

mapping clause assembly = PEXT_SHIFT_SAT_B(imm3, rs1, rd, p_inst)
  <-> p_shift_sat_b_mapping(p_inst) ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ hex_bits_3(imm3)

/* ****************************************************************** */

union clause ast = PEXT_SHIFT_SAT_H : (bits(4), regidx, regidx, p_shift_sat_h)

mapping clause encdec = PEXT_SHIFT_SAT_H(imm4, rs1, rd, PSRLI_H) <->
  0b1 @ 0b000 @ 0b0 @ 0b001 @ imm4 @ rs1 @ 0b100 @ rd @ 0b0011011
mapping clause encdec = PEXT_SHIFT_SAT_H(imm4, rs1, rd, PUSATI_H) <->
  0b1 @ 0b010 @ 0b0 @ 0b001 @ imm4 @ rs1 @ 0b100 @ rd @ 0b0011011
mapping clause encdec = PEXT_SHIFT_SAT_H(imm4, rs1, rd, PSRAI_H) <->
  0b1 @ 0b100 @ 0b0 @ 0b001 @ imm4 @ rs1 @ 0b100 @ rd @ 0b0011011
mapping clause encdec = PEXT_SHIFT_SAT_H(imm4, rs1, rd, PSRARI_H) <->
  0b1 @ 0b101 @ 0b0 @ 0b001 @ imm4 @ rs1 @ 0b100 @ rd @ 0b0011011
mapping clause encdec = PEXT_SHIFT_SAT_H(imm4, rs1, rd, PSATI_H) <->
  0b1 @ 0b110 @ 0b0 @ 0b001 @ imm4 @ rs1 @ 0b100 @ rd @ 0b0011011

function clause execute (PEXT_SHIFT_SAT_H(imm4, rs1, rd, op)) = {
  let rs1_val = X(rs1);
  let sa : bits(8) = EXTZ(imm4);
  var result : xlenbits = zeros();
  foreach (i from 0 to (sizeof(xlen) - 16) by 16) {
    let rs1_halfword = slice(rs1_val, i, 16);
    result[(i+15)..i] = match op {
      PSRLI_H => shift_right_logic(rs1_halfword, sa),
      PUSATI_H =>
        let maxval : bits(16) = ~(0xFFFF << sa) in
        if (rs1_halfword <_s 0x0000) then 0x0000
        else if (rs1_halfword >_s maxval) then maxval else rs1_halfword,
      PSRAI_H => shift_right_arith(rs1_halfword, sa),
      PSRARI_H => shift_right_arith_rounding(rs1_halfword, sa),
      PSATI_H =>
        let minval : bits(16) = 0xFFFF << sa in
        let maxval = ~(minval) in
        if (rs1_halfword <_s minval) then minval
        else if (rs1_halfword >_s maxval) then maxval else rs1_halfword,
    };
  };
  X(rd) = result;
  RETIRE_SUCCESS
}

mapping p_shift_sat_h_mapping : p_shift_sat_h <-> string = {
  PSRLI_H <-> "psrli.h",
  PUSATI_H <-> "pusati.h",
  PSRAI_H <-> "psrai.h",
  PSRARI_H <-> "psrari.h",
  PSATI_H <-> "psati.h"
}

mapping clause assembly = PEXT_SHIFT_SAT_H(imm4, rs1, rd, p_inst)
  <-> p_shift_sat_h_mapping(p_inst) ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ hex_bits_4(imm4)

/* ****************************************************************** */

union clause ast = PEXT_SHIFT_SAT_W : (bits(5), regidx, regidx, p_shift_sat_w)

mapping clause encdec = PEXT_SHIFT_SAT_W(imm5, rs1, rd, PSRLI_W) <->
  0b1 @ 0b000 @ 0b0 @ 0b01 @ imm5 @ rs1 @ 0b100 @ rd @ 0b0011011
mapping clause encdec = PEXT_SHIFT_SAT_W(imm5, rs1, rd, PUSATI_W) <->
  0b1 @ 0b010 @ 0b0 @ 0b01 @ imm5 @ rs1 @ 0b100 @ rd @ 0b0011011
mapping clause encdec = PEXT_SHIFT_SAT_W(imm5, rs1, rd, PSRAI_W) <->
  0b1 @ 0b100 @ 0b0 @ 0b01 @ imm5 @ rs1 @ 0b100 @ rd @ 0b0011011
mapping clause encdec = PEXT_SHIFT_SAT_W(imm5, rs1, rd, PSRARI_W) <->
  0b1 @ 0b101 @ 0b0 @ 0b01 @ imm5 @ rs1 @ 0b100 @ rd @ 0b0011011
mapping clause encdec = PEXT_SHIFT_SAT_W(imm5, rs1, rd, PSATI_W) <->
  0b1 @ 0b110 @ 0b0 @ 0b01 @ imm5 @ rs1 @ 0b100 @ rd @ 0b0011011

function clause execute (PEXT_SHIFT_SAT_W(imm5, rs1, rd, op)) = {
  let rs1_val = X(rs1);
  let sa : bits(8) = EXTZ(imm5);
  var result : xlenbits = zeros();
  foreach (i from 0 to (sizeof(xlen) - 32) by 32) {
    let rs1_word = slice(rs1_val, i, 32);
    result[(i+31)..i] = match op {
      PSRLI_W => shift_right_logic(rs1_word, sa),
      PUSATI_W =>
        let maxval : bits(32) = ~(0xFFFFFFFF << sa) in
        if (rs1_word <_s 0x00000000) then 0x00000000
        else if (rs1_word >_s maxval) then maxval else rs1_word,
      PSRAI_W => shift_right_arith(rs1_word, sa),
      PSRARI_W => shift_right_arith_rounding(rs1_word, sa),
      PSATI_W =>
        let minval : bits(32) = 0xFFFFFFFF << sa in
        let maxval = ~(minval) in
        if (rs1_word <_s minval) then minval
        else if (rs1_word >_s maxval) then maxval else rs1_word,
    };
  };
  X(rd) = result;
  RETIRE_SUCCESS
}

mapping p_shift_sat_w_mapping : p_shift_sat_w <-> string = {
  PSRLI_W <-> "psrli.w",
  PUSATI_W <-> "pusati.w",
  PSRAI_W <-> "psrai.w",
  PSRARI_W <-> "psrari.w",
  PSATI_W <-> "psati.w"
}

mapping clause assembly = PEXT_SHIFT_SAT_W(imm5, rs1, rd, p_inst)
  <-> p_shift_sat_w_mapping(p_inst) ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ hex_bits_5(imm5)

/* ****************************************************************** */

union clause ast = PEXT_SHIFT_SUM : (regidx, regidx, regidx, p_shift_sum)

mapping clause encdec = PEXT_SHIFT_SUM(rs1, rs2, rd, PSRL_B_B0) <->
  0b1 @ 0b000 @ 0b1 @ 0b10 @ rs2 @ rs1 @ 0b100 @ rd @ 0b0011011
mapping clause encdec = PEXT_SHIFT_SUM(rs1, rs2, rd, PSRA_B_B0) <->
  0b1 @ 0b100 @ 0b1 @ 0b10 @ rs2 @ rs1 @ 0b100 @ rd @ 0b0011011
mapping clause encdec = PEXT_SHIFT_SUM(rs1, rs2, rd, PSRL_H_H0) <->
  0b1 @ 0b000 @ 0b1 @ 0b00 @ rs2 @ rs1 @ 0b100 @ rd @ 0b0011011
mapping clause encdec = PEXT_SHIFT_SUM(rs1, rs2, rd, PSRA_H_H0) <->
  0b1 @ 0b100 @ 0b1 @ 0b00 @ rs2 @ rs1 @ 0b100 @ rd @ 0b0011011
mapping clause encdec = PEXT_SHIFT_SUM(rs1, rs2, rd, PSRL_W_W0) if sizeof(xlen) == 64 <->
  0b1 @ 0b000 @ 0b1 @ 0b01 @ rs2 @ rs1 @ 0b100 @ rd @ 0b0011011 if sizeof(xlen) == 64
mapping clause encdec = PEXT_SHIFT_SUM(rs1, rs2, rd, PSRA_W_W0) if sizeof(xlen) == 64 <->
  0b1 @ 0b100 @ 0b1 @ 0b01 @ rs2 @ rs1 @ 0b100 @ rd @ 0b0011011 if sizeof(xlen) == 64
mapping clause encdec = PEXT_SHIFT_SUM(rs1, rs2, rd, PREDSUM_H) <->
  0b1 @ 0b001 @ 0b1 @ 0b00 @ rs2 @ rs1 @ 0b100 @ rd @ 0b0011011
mapping clause encdec = PEXT_SHIFT_SUM(rs1, rs2, rd, PREDSUMU_H) <->
  0b1 @ 0b011 @ 0b1 @ 0b00 @ rs2 @ rs1 @ 0b100 @ rd @ 0b0011011
mapping clause encdec = PEXT_SHIFT_SUM(rs1, rs2, rd, PREDSUM_W) if sizeof(xlen) == 64 <->
  0b1 @ 0b001 @ 0b1 @ 0b01 @ rs2 @ rs1 @ 0b100 @ rd @ 0b0011011 if sizeof(xlen) == 64
mapping clause encdec = PEXT_SHIFT_SUM(rs1, rs2, rd, PREDSUMU_W) if sizeof(xlen) == 64 <->
  0b1 @ 0b011 @ 0b1 @ 0b01 @ rs2 @ rs1 @ 0b100 @ rd @ 0b0011011 if sizeof(xlen) == 64

function clause execute (PEXT_SHIFT_SUM(rs1, rs2, rd, op)) = {
  let rs1_val = X(rs1);
  let rs2_val = X(rs2);
  var result : xlenbits = zeros();
  match op {
    PSRL_B_B0 => {
      foreach (i from 0 to (sizeof(xlen) - 8) by 8) {
        let rs1_byte = slice(rs1_val, i, 8);
        result[(i+7)..i] = shift_right_logic(rs1_byte, EXTZ(rs2_val[2..0]));
      };
    },
    PSRA_B_B0 => {
      foreach (i from 0 to (sizeof(xlen) - 8) by 8) {
        let rs1_byte = slice(rs1_val, i, 8);
        result[(i+7)..i] = shift_right_arith(rs1_byte, EXTZ(rs2_val[2..0]));
      };
    },
    PSRL_H_H0 => {
      foreach (i from 0 to (sizeof(xlen) - 16) by 16) {
        let rs1_halfword = slice(rs1_val, i, 16);
        result[(i+15)..i] = shift_right_logic(rs1_halfword, EXTZ(rs2_val[3..0]));
      };
    },
    PSRA_H_H0 => {
      foreach (i from 0 to (sizeof(xlen) - 16) by 16) {
        let rs1_halfword = slice(rs1_val, i, 16);
        result[(i+15)..i] = shift_right_arith(rs1_halfword, EXTZ(rs2_val[3..0]));
      };
    },
    PSRL_W_W0 => {
      foreach (i from 0 to (sizeof(xlen) - 32) by 32) {
        let rs1_word = slice(rs1_val, i, 32);
        result[(i+31)..i] = shift_right_logic(rs1_word, EXTZ(rs2_val[4..0]));
      };
    },
    PSRA_W_W0 => {
      foreach (i from 0 to (sizeof(xlen) - 32) by 32) {
        let rs1_word = slice(rs1_val, i, 32);
        result[(i+31)..i] = shift_right_arith(rs1_word, EXTZ(rs2_val[4..0]));
      };
    },
    PREDSUM_H => {
      let s1 = X(rs1);
      var sum : bits(xlen) = X(rs2);
      foreach (i from 0 to (sizeof(xlen) - 16) by 16) {
          let s1_h = s1[(i+15)..i];
          sum = sum + EXTS(sizeof(xlen), s1_h);
      };
      result = sum;
    },
    PREDSUMU_H => {
      let s1 = X(rs1);
      var sum : bits(xlen) = X(rs2);
      foreach (i from 0 to (sizeof(xlen) - 16) by 16) {
          let s1_h = s1[(i+15)..i];
          sum = sum + EXTZ(sizeof(xlen), s1_h);
      };
      result = sum;
    },
    PREDSUM_W => {
      let s1 = X(rs1);
      var sum : bits(xlen) = X(rs2);
      foreach (i from 0 to (sizeof(xlen) - 32) by 32) {
          let s1_h = s1[(i+31)..i];
          sum = sum + EXTS(sizeof(xlen), s1_h);
      };
      result = sum;
    },
    PREDSUMU_W => {
      let s1 = X(rs1);
      var sum : bits(xlen) = X(rs2);
      foreach (i from 0 to (sizeof(xlen) - 32) by 32) {
          let s1_h = s1[(i+31)..i];
          sum = sum + EXTZ(sizeof(xlen), s1_h);
      };
      result = sum;
    }
  };
  X(rd) = result;
  RETIRE_SUCCESS
}

mapping p_shift_sum_mapping : p_shift_sum <-> string = {
  PSRL_B_B0 <-> "psrl.b.b0",
  PSRA_B_B0 <-> "psra.b.b0",
  PSRL_H_H0 <-> "psrl.h.h0",
  PSRA_H_H0 <-> "psra.h.h0",
  PSRL_W_W0 <-> "psrl.w.w0",
  PSRA_W_W0 <-> "psra.w.w0",
  PREDSUM_H <-> "predsum.h",
  PREDSUMU_H <-> "predsumu.h",
  PREDSUM_W <-> "predsum.w",
  PREDSUMU_W <-> "predsumu.w"
}

mapping clause assembly = PEXT_SHIFT_SUM(rs1, rs2, rd, p_inst)
  <-> p_shift_sum_mapping(p_inst) ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2) // TODO: The order is probably correct, but we still have to check.

