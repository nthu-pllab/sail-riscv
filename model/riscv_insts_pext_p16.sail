union clause ast = PEXT_ADDSUB_H : (regidx, regidx, regidx, p_addsub_h)

mapping clause encdec = PEXT_ADDSUB_H(rs1, rs2, rd, PAS_HX) <->
  0b1 @ 0b0000 @ 0b00 @ rs2 @ rs1 @ 0b110 @ rd @ 0b0111011
mapping clause encdec = PEXT_ADDSUB_H(rs1, rs2, rd, PSA_HX) <->
  0b1 @ 0b0000 @ 0b10 @ rs2 @ rs1 @ 0b110 @ rd @ 0b0111011
mapping clause encdec = PEXT_ADDSUB_H(rs1, rs2, rd, PSAS_HX) <->
  0b1 @ 0b0010 @ 0b00 @ rs2 @ rs1 @ 0b110 @ rd @ 0b0111011
mapping clause encdec = PEXT_ADDSUB_H(rs1, rs2, rd, PSSA_HX) <->
  0b1 @ 0b0010 @ 0b10 @ rs2 @ rs1 @ 0b110 @ rd @ 0b0111011
mapping clause encdec = PEXT_ADDSUB_H(rs1, rs2, rd, PAAS_HX) <->
  0b1 @ 0b0011 @ 0b00 @ rs2 @ rs1 @ 0b110 @ rd @ 0b0111011
mapping clause encdec = PEXT_ADDSUB_H(rs1, rs2, rd, PASA_HX) <->
  0b1 @ 0b0011 @ 0b10 @ rs2 @ rs1 @ 0b110 @ rd @ 0b0111011

function clause execute (PEXT_ADDSUB_H(rs1, rs2, rd, op)) = {
  let rs1_val = X(rs1);
  let rs2_val = X(rs2);
  var result : xlenbits = zeros();
  foreach (i from 0 to (sizeof(xlen) - 32) by 32) {
    let rs1_halfword_even = slice(rs1_val, i, 16);
    let rs2_halfword_even = slice(rs2_val, i, 16);
    let rs1_halfword_odd = slice(rs1_val, i + 16, 16);
    let rs2_halfword_odd = slice(rs2_val, i + 16, 16);
    result[(i+31)..i] = match op {
      PAS_HX => (rs1_halfword_odd + rs2_halfword_even) @ (rs1_halfword_even - rs2_halfword_odd),
      PSA_HX => (rs1_halfword_odd - rs2_halfword_even) @ (rs1_halfword_even + rs2_halfword_odd),
      PSAS_HX => sadd(rs1_halfword_odd, rs2_halfword_even) @ ssub(rs1_halfword_even, rs2_halfword_odd),
      PSSA_HX => ssub(rs1_halfword_odd, rs2_halfword_even) @ sadd(rs1_halfword_even, rs2_halfword_odd),
      PAAS_HX => aadd(rs1_halfword_odd, rs2_halfword_even) @ asub(rs1_halfword_even, rs2_halfword_odd),
      PASA_HX => asub(rs1_halfword_odd, rs2_halfword_even) @ aadd(rs1_halfword_even, rs2_halfword_odd)
    };
  };
  X(rd) = result;
  RETIRE_SUCCESS
}

mapping p_addsub_h_mapping : p_addsub_h <-> string = {
  PAS_HX <-> "pas.hx",
  PSA_HX <-> "psa.hx",
  PSAS_HX <-> "psas.hx",
  PSSA_HX <-> "pssa.hx",
  PAAS_HX <-> "paas.hx",
  PASA_HX <-> "pasa.hx"
}

mapping clause assembly = PEXT_ADDSUB_H(rs1, rs2, rd, p_inst)
  <-> p_addsub_h_mapping(p_inst) ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)

/* ****************************************************************** */

union clause ast = PEXT_COMPARISON_B : (regidx, regidx, regidx, p_comparison_b)

mapping clause encdec = PEXT_COMPARISON_B(rs1, rs2, rd, PMSEQ_B) <->
  0b1 @ 0b1000 @ 0b10 @ rs2 @ rs1 @ 0b110 @ rd @ 0b0111011
mapping clause encdec = PEXT_COMPARISON_B(rs1, rs2, rd, PMSLT_B) <->
  0b1 @ 0b1010 @ 0b10 @ rs2 @ rs1 @ 0b110 @ rd @ 0b0111011
mapping clause encdec = PEXT_COMPARISON_B(rs1, rs2, rd, PMSLTU_B) <->
  0b1 @ 0b1011 @ 0b10 @ rs2 @ rs1 @ 0b110 @ rd @ 0b0111011
mapping clause encdec = PEXT_COMPARISON_B(rs1, rs2, rd, PMIN_B) <->
  0b1 @ 0b1100 @ 0b10 @ rs2 @ rs1 @ 0b110 @ rd @ 0b0111011
mapping clause encdec = PEXT_COMPARISON_B(rs1, rs2, rd, PMINU_B) <->
  0b1 @ 0b1101 @ 0b10 @ rs2 @ rs1 @ 0b110 @ rd @ 0b0111011
mapping clause encdec = PEXT_COMPARISON_B(rs1, rs2, rd, PMAX_B) <->
  0b1 @ 0b1110 @ 0b10 @ rs2 @ rs1 @ 0b110 @ rd @ 0b0111011
mapping clause encdec = PEXT_COMPARISON_B(rs1, rs2, rd, PMAXU_B) <->
  0b1 @ 0b1111 @ 0b10 @ rs2 @ rs1 @ 0b110 @ rd @ 0b0111011

function clause execute (PEXT_COMPARISON_B(rs1, rs2, rd, op)) = {
  let rs1_val = X(rs1);
  let rs2_val = X(rs2);
  var result : xlenbits = zeros();
  foreach (i from 0 to (sizeof(xlen) - 8) by 8) {
    let rs1_byte = slice(rs1_val, i, 8);
    let rs2_byte = slice(rs2_val, i, 8);
    result[(i+7)..i] = match op {
      PMSEQ_B => mseq(rs1_byte, rs2_byte),
      PMSLT_B => mslt(rs1_byte, rs2_byte),
      PMSLTU_B => msltu(rs1_byte, rs2_byte),
      PMIN_B => mins(rs1_byte, rs2_byte),
      PMINU_B => minu(rs1_byte, rs2_byte),
      PMAX_B => maxs(rs1_byte, rs2_byte),
      PMAXU_B => maxu(rs1_byte, rs2_byte)
    };
  };
  X(rd) = result;
  RETIRE_SUCCESS
}

mapping p_comparison_b_mapping : p_comparison_b <-> string = {
  PMSEQ_B <-> "pmseq.b",
  PMSLT_B <-> "pmslt.b",
  PMSLTU_B <-> "pmsltu.b",
  PMIN_B <-> "pmin.b",
  PMINU_B <-> "pmin.b",
  PMAX_B <-> "pmax.b",
  PMAXU_B <-> "pmax.b"
}

mapping clause assembly = PEXT_COMPARISON_B(rs1, rs2, rd, p_inst)
  <-> p_comparison_b_mapping(p_inst) ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2) // TODO: The order is probably correct, but we still have to check.


/* ****************************************************************** */

union clause ast = PEXT_COMPARISON_H : (regidx, regidx, regidx, p_comparison_h)

mapping clause encdec = PEXT_COMPARISON_H(rs1, rs2, rd, PMSEQ_H) <->
  0b1 @ 0b1000 @ 0b00 @ rs2 @ rs1 @ 0b110 @ rd @ 0b0111011
mapping clause encdec = PEXT_COMPARISON_H(rs1, rs2, rd, PMSLT_H) <->
  0b1 @ 0b1010 @ 0b00 @ rs2 @ rs1 @ 0b110 @ rd @ 0b0111011
mapping clause encdec = PEXT_COMPARISON_H(rs1, rs2, rd, PMSLTU_H) <->
  0b1 @ 0b1011 @ 0b00 @ rs2 @ rs1 @ 0b110 @ rd @ 0b0111011
mapping clause encdec = PEXT_COMPARISON_H(rs1, rs2, rd, PMIN_H) <->
  0b1 @ 0b1100 @ 0b00 @ rs2 @ rs1 @ 0b110 @ rd @ 0b0111011
mapping clause encdec = PEXT_COMPARISON_H(rs1, rs2, rd, PMINU_H) <->
  0b1 @ 0b1101 @ 0b00 @ rs2 @ rs1 @ 0b110 @ rd @ 0b0111011
mapping clause encdec = PEXT_COMPARISON_H(rs1, rs2, rd, PMAX_H) <->
  0b1 @ 0b1110 @ 0b00 @ rs2 @ rs1 @ 0b110 @ rd @ 0b0111011
mapping clause encdec = PEXT_COMPARISON_H(rs1, rs2, rd, PMAXU_H) <->
  0b1 @ 0b1111 @ 0b00 @ rs2 @ rs1 @ 0b110 @ rd @ 0b0111011

function clause execute (PEXT_COMPARISON_H(rs1, rs2, rd, op)) = {
  let rs1_val = X(rs1);
  let rs2_val = X(rs2);
  var result : xlenbits = zeros();
  foreach (i from 0 to (sizeof(xlen) - 16) by 16) {
    let rs1_halfword = slice(rs1_val, i, 16);
    let rs2_halfword = slice(rs2_val, i, 16);
    result[(i+15)..i] = match op {
      PMSEQ_H => mseq(rs1_halfword, rs2_halfword),
      PMSLT_H => mslt(rs1_halfword, rs2_halfword),
      PMSLTU_H => msltu(rs1_halfword, rs2_halfword),
      PMIN_H => mins(rs1_halfword, rs2_halfword),
      PMINU_H => minu(rs1_halfword, rs2_halfword),
      PMAX_H => maxs(rs1_halfword, rs2_halfword),
      PMAXU_H => maxu(rs1_halfword, rs2_halfword)
    };
  };
  X(rd) = result;
  RETIRE_SUCCESS
}

mapping p_comparison_h_mapping : p_comparison_h <-> string = {
  PMSEQ_H <-> "pmseq.h",
  PMSLT_H <-> "pmslt.h",
  PMSLTU_H <-> "pmsltu.h",
  PMIN_H <-> "pmin.h",
  PMINU_H <-> "pmin.h",
  PMAX_H <-> "pmax.h",
  PMAXU_H <-> "pmax.h"
}

mapping clause assembly = PEXT_COMPARISON_H(rs1, rs2, rd, p_inst)
  <-> p_comparison_h_mapping(p_inst) ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2) // TODO: The order is probably correct, but we still have to check.

/* ****************************************************************** */

union clause ast = PEXT_COMPARISON_W : (regidx, regidx, regidx, p_comparison_w)

mapping clause encdec = PEXT_COMPARISON_W(rs1, rs2, rd, MSEQ) if sizeof(xlen) == 32 <->
  0b1 @ 0b1000 @ 0b01 @ rs2 @ rs1 @ 0b110 @ rd @ 0b0111011 if sizeof(xlen) == 32
mapping clause encdec = PEXT_COMPARISON_W(rs1, rs2, rd, PMSEQ_W) if sizeof(xlen) == 64 <->
  0b1 @ 0b1000 @ 0b01 @ rs2 @ rs1 @ 0b110 @ rd @ 0b0111011 if sizeof(xlen) == 64
mapping clause encdec = PEXT_COMPARISON_W(rs1, rs2, rd, MSLT) if sizeof(xlen) == 32 <->
  0b1 @ 0b1010 @ 0b01 @ rs2 @ rs1 @ 0b110 @ rd @ 0b0111011 if sizeof(xlen) == 32
mapping clause encdec = PEXT_COMPARISON_W(rs1, rs2, rd, PMSLT_W) if sizeof(xlen) == 64 <->
  0b1 @ 0b1010 @ 0b01 @ rs2 @ rs1 @ 0b110 @ rd @ 0b0111011 if sizeof(xlen) == 64
mapping clause encdec = PEXT_COMPARISON_W(rs1, rs2, rd, MSLTU) if sizeof(xlen) == 32 <->
  0b1 @ 0b1011 @ 0b01 @ rs2 @ rs1 @ 0b110 @ rd @ 0b0111011 if sizeof(xlen) == 32
mapping clause encdec = PEXT_COMPARISON_W(rs1, rs2, rd, PMSLTU_W) if sizeof(xlen) == 64 <->
  0b1 @ 0b1011 @ 0b01 @ rs2 @ rs1 @ 0b110 @ rd @ 0b0111011 if sizeof(xlen) == 64
mapping clause encdec = PEXT_COMPARISON_W(rs1, rs2, rd, PMIN_W) if sizeof(xlen) == 64 <->
  0b1 @ 0b1100 @ 0b01 @ rs2 @ rs1 @ 0b110 @ rd @ 0b0111011 if sizeof(xlen) == 64
mapping clause encdec = PEXT_COMPARISON_W(rs1, rs2, rd, PMINU_W) if sizeof(xlen) == 64 <->
  0b1 @ 0b1101 @ 0b01 @ rs2 @ rs1 @ 0b110 @ rd @ 0b0111011 if sizeof(xlen) == 64
mapping clause encdec = PEXT_COMPARISON_W(rs1, rs2, rd, PMAX_W) if sizeof(xlen) == 64 <->
  0b1 @ 0b1110 @ 0b01 @ rs2 @ rs1 @ 0b110 @ rd @ 0b0111011 if sizeof(xlen) == 64
mapping clause encdec = PEXT_COMPARISON_W(rs1, rs2, rd, PMAXU_W) if sizeof(xlen) == 64 <->
  0b1 @ 0b1111 @ 0b01 @ rs2 @ rs1 @ 0b110 @ rd @ 0b0111011 if sizeof(xlen) == 64

function clause execute (PEXT_COMPARISON_W(rs1, rs2, rd, op)) = {
  let rs1_val = X(rs1);
  let rs2_val = X(rs2);
  var result : xlenbits = zeros();
  foreach (i from 0 to (sizeof(xlen) - 32) by 32) {
    let rs1_word = slice(rs1_val, i, 32);
    let rs2_word = slice(rs2_val, i, 32);
    result[(i+31)..i] = match op {
      MSEQ => mseq(rs1_word, rs2_word),
      PMSEQ_W => mseq(rs1_word, rs2_word),
      MSLT => mslt(rs1_word, rs2_word),
      PMSLT_W => mslt(rs1_word, rs2_word),
      MSLTU => msltu(rs1_word, rs2_word),
      PMSLTU_W => msltu(rs1_word, rs2_word),
      PMIN_W => mins(rs1_word, rs2_word),
      PMINU_W => minu(rs1_word, rs2_word),
      PMAX_W => maxs(rs1_word, rs2_word),
      PMAXU_W => maxu(rs1_word, rs2_word)
    };
  };
  X(rd) = result;
  RETIRE_SUCCESS
}

mapping p_comparison_w_mapping : p_comparison_w <-> string = {
  MSEQ <-> "mseq",
  PMSEQ_W <-> "pmseq.w",
  MSLT <-> "mslt",
  PMSLT_W <-> "pmslt.w",
  MSLTU <-> "msltu",
  PMSLTU_W <-> "pmsltu.w",
  PMIN_W <-> "pmin.w",
  PMINU_W <-> "pmin.w",
  PMAX_W <-> "pmax.w",
  PMAXU_W <-> "pmax.w"
}

mapping clause assembly = PEXT_COMPARISON_W(rs1, rs2, rd, p_inst)
  <-> p_comparison_w_mapping(p_inst) ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2) // TODO: The order is probably correct, but we still have to check.
