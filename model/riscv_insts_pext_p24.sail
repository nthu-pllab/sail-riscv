union clause ast = PEXT_PACK_H_RV32 : (pregidx, pregidx, pregidx, p_pack_h_rv32)

mapping clause encdec = PEXT_PACK_H_RV32(rs1p, rs2p, rdp, PPACK_DH) <->
  0b1 @ 0b000 @ 0b0 @ 0b00 @ rs2p @ 0b0 @ rs1p @ 0b1110 @ rdp @ 0b00011011
mapping clause encdec = PEXT_PACK_H_RV32(rs1p, rs2p, rdp, PPACKBT_DH) <->
  0b1 @ 0b001 @ 0b0 @ 0b00 @ rs2p @ 0b0 @ rs1p @ 0b1110 @ rdp @ 0b00011011
mapping clause encdec = PEXT_PACK_H_RV32(rs1p, rs2p, rdp, PPACKTB_DH) <->
  0b1 @ 0b010 @ 0b0 @ 0b00 @ rs2p @ 0b0 @ rs1p @ 0b1110 @ rdp @ 0b00011011
mapping clause encdec = PEXT_PACK_H_RV32(rs1p, rs2p, rdp, PPACKT_DH) <->
  0b1 @ 0b011 @ 0b0 @ 0b00 @ rs2p @ 0b0 @ rs1p @ 0b1110 @ rdp @ 0b00011011

function clause execute (PEXT_PACK_H_RV32(rs1p, rs2p, rdp, op)) = {
  let rs1_val = X(rs1p @ 0b1) @ X(rs1p @ 0b0);
  let rs2_val = X(rs2p @ 0b1) @ X(rs2p @ 0b0);
  var result : bits(64) = zeros();
  foreach (i from 0 to (64 - 16) by 16) {
    let rs1_byte_even = slice(rs1_val, i, 8);
    let rs2_byte_even = slice(rs2_val, i, 8);
    let rs1_byte_odd = slice(rs1_val, i + 8, 8);
    let rs2_byte_odd = slice(rs2_val, i + 8, 8);
    result[(i+15)..i] = match op {
      PPACK_DH => rs2_byte_even @ rs1_byte_even,
      PPACKBT_DH => rs2_byte_odd @ rs1_byte_even,
      PPACKTB_DH => rs2_byte_even @ rs1_byte_odd,
      PPACKT_DH => rs2_byte_odd @ rs1_byte_odd
    };
  };
  X(rdp @ 0b1) = result[63..32];
  X(rdp @ 0b0) = result[31..0];
  RETIRE_SUCCESS
}

mapping p_pack_h_rv32_mapping : p_pack_h_rv32 <-> string = {
  PPACK_DH <-> "ppack.dh",
  PPACKBT_DH <-> "ppackbt.dh",
  PPACKTB_DH <-> "ppacktb.dh",
  PPACKT_DH <-> "ppackt.dh"
}

mapping clause assembly = PEXT_PACK_H_RV32(rs1p, rs2p, rdp, p_inst)
  <-> p_pack_h_rv32_mapping(p_inst) ^ spc() ^ preg_name(rdp) ^ sep() ^ preg_name(rs1p) ^ sep() ^ preg_name(rs2p)

/* ****************************************************************** */

union clause ast = PEXT_PACK_W_RV32 : (pregidx, pregidx, pregidx, p_pack_w_rv32)

mapping clause encdec = PEXT_PACK_W_RV32(rs1p, rs2p, rdp, PPACK_DW) <->
  0b1 @ 0b000 @ 0b0 @ 0b01 @ rs2p @ 0b0 @ rs1p @ 0b1110 @ rdp @ 0b00011011
mapping clause encdec = PEXT_PACK_W_RV32(rs1p, rs2p, rdp, PPACKBT_DW) <->
  0b1 @ 0b001 @ 0b0 @ 0b01 @ rs2p @ 0b0 @ rs1p @ 0b1110 @ rdp @ 0b00011011
mapping clause encdec = PEXT_PACK_W_RV32(rs1p, rs2p, rdp, PPACKTB_DW) <->
  0b1 @ 0b010 @ 0b0 @ 0b01 @ rs2p @ 0b0 @ rs1p @ 0b1110 @ rdp @ 0b00011011
mapping clause encdec = PEXT_PACK_W_RV32(rs1p, rs2p, rdp, PPACKT_DW) <->
  0b1 @ 0b011 @ 0b0 @ 0b01 @ rs2p @ 0b0 @ rs1p @ 0b1110 @ rdp @ 0b00011011

function clause execute (PEXT_PACK_W_RV32(rs1p, rs2p, rdp, op)) = {
  let rs1_val = X(rs1p @ 0b1) @ X(rs1p @ 0b0);
  let rs2_val = X(rs2p @ 0b1) @ X(rs2p @ 0b0);
  var result : bits(64) = zeros();
  foreach (i from 0 to (64 - 32) by 32) {
    let rs1_halfword_even = slice(rs1_val, i, 16);
    let rs2_halfword_even = slice(rs2_val, i, 16);
    let rs1_halfword_odd = slice(rs1_val, i + 16, 16);
    let rs2_halfword_odd = slice(rs2_val, i + 16, 16);
    result[(i+31)..i] = match op {
      PPACK_DW => rs2_halfword_even @ rs1_halfword_even,
      PPACKBT_DW => rs2_halfword_odd @ rs1_halfword_even,
      PPACKTB_DW => rs2_halfword_even @ rs1_halfword_odd,
      PPACKT_DW => rs2_halfword_odd @ rs1_halfword_odd
    };
  };
  X(rdp @ 0b1) = result[63..32];
  X(rdp @ 0b0) = result[31..0];
  RETIRE_SUCCESS
}

mapping p_pack_w_rv32_mapping : p_pack_w_rv32 <-> string = {
  PPACK_DW <-> "ppack.dw",
  PPACKBT_DW <-> "ppackbt.dw",
  PPACKTB_DW <-> "ppacktb.dw",
  PPACKT_DW <-> "ppackt.dw"
}

mapping clause assembly = PEXT_PACK_W_RV32(rs1p, rs2p, rdp, p_inst)
  <-> p_pack_w_rv32_mapping(p_inst) ^ spc() ^ preg_name(rdp) ^ sep() ^ preg_name(rs1p) ^ sep() ^ preg_name(rs2p)

/* ****************************************************************** */

union clause ast = PEXT_ADDSUB_H_RV32 : (pregidx, pregidx, pregidx, p_addsub_h_rv32)

mapping clause encdec = PEXT_ADDSUB_H_RV32(rs1p, rs2p, rdp, PAS_DHX) <->
  0b1 @ 0b0000 @ 0b00 @ rs2p @ 0b1 @ rs1p @ 0b1110 @ rdp @ 0b00011011
mapping clause encdec = PEXT_ADDSUB_H_RV32(rs1p, rs2p, rdp, PSA_DHX) <->
  0b1 @ 0b0000 @ 0b10 @ rs2p @ 0b1 @ rs1p @ 0b1110 @ rdp @ 0b00011011
mapping clause encdec = PEXT_ADDSUB_H_RV32(rs1p, rs2p, rdp, PSAS_DHX) <->
  0b1 @ 0b0010 @ 0b00 @ rs2p @ 0b1 @ rs1p @ 0b1110 @ rdp @ 0b00011011
mapping clause encdec = PEXT_ADDSUB_H_RV32(rs1p, rs2p, rdp, PSSA_DHX) <->
  0b1 @ 0b0010 @ 0b10 @ rs2p @ 0b1 @ rs1p @ 0b1110 @ rdp @ 0b00011011
mapping clause encdec = PEXT_ADDSUB_H_RV32(rs1p, rs2p, rdp, PAAS_DHX) <->
  0b1 @ 0b0011 @ 0b00 @ rs2p @ 0b1 @ rs1p @ 0b1110 @ rdp @ 0b00011011
mapping clause encdec = PEXT_ADDSUB_H_RV32(rs1p, rs2p, rdp, PASA_DHX) <->
  0b1 @ 0b0011 @ 0b10 @ rs2p @ 0b1 @ rs1p @ 0b1110 @ rdp @ 0b00011011

function clause execute (PEXT_ADDSUB_H_RV32(rs1p, rs2p, rdp, op)) = {
  let rs1_val = X(rs1p @ 0b1) @ X(rs1p @ 0b0);
  let rs2_val = X(rs2p @ 0b1) @ X(rs2p @ 0b0);
  var result : bits(64) = zeros();
  foreach (i from 0 to (64 - 32) by 32) {
    let rs1_halfword_even = slice(rs1_val, i, 16);
    let rs2_halfword_even = slice(rs2_val, i, 16);
    let rs1_halfword_odd = slice(rs1_val, i + 16, 16);
    let rs2_halfword_odd = slice(rs2_val, i + 16, 16);
    result[(i+31)..i] = match op {
      PAS_DHX => (rs1_halfword_odd + rs2_halfword_even) @ (rs1_halfword_even - rs2_halfword_odd),
      PSA_DHX => (rs1_halfword_odd - rs2_halfword_even) @ (rs1_halfword_even + rs2_halfword_odd),
      PSAS_DHX => sadd(rs1_halfword_odd, rs2_halfword_even) @ ssub(rs1_halfword_even, rs2_halfword_odd),
      PSSA_DHX => ssub(rs1_halfword_odd, rs2_halfword_even) @ sadd(rs1_halfword_even, rs2_halfword_odd),
      PAAS_DHX => aadd(rs1_halfword_odd, rs2_halfword_even) @ asub(rs1_halfword_even, rs2_halfword_odd),
      PASA_DHX => asub(rs1_halfword_odd, rs2_halfword_even) @ aadd(rs1_halfword_even, rs2_halfword_odd)
    };
  };
  X(rdp @ 0b1) = result[63..32];
  X(rdp @ 0b0) = result[31..0];
  RETIRE_SUCCESS
}

mapping p_addsub_h_rv32_mapping : p_addsub_h_rv32 <-> string = {
  PAS_DHX <-> "pas.dhx",
  PSA_DHX <-> "psa.dhx",
  PSAS_DHX <-> "psas.dhx",
  PSSA_DHX <-> "pssa.dhx",
  PAAS_DHX <-> "paas.dhx",
  PASA_DHX <-> "pasa.dhx"
}

mapping clause assembly = PEXT_ADDSUB_H_RV32(rs1p, rs2p, rdp, p_inst)
  <-> p_addsub_h_rv32_mapping(p_inst) ^ spc() ^ preg_name(rdp) ^ sep() ^ preg_name(rs1p) ^ sep() ^ preg_name(rs2p)

/* ****************************************************************** */

union clause ast = PEXT_COMPARISON_B_RV32 : (pregidx, pregidx, pregidx, p_comparison_b_rv32)

mapping clause encdec = PEXT_COMPARISON_B_RV32(rs1p, rs2p, rdp, PMSEQ_DB) <->
  0b1 @ 0b1000 @ 0b10 @ rs2p @ 0b1 @ rs1p @ 0b1110 @ rdp @ 0b00011011
mapping clause encdec = PEXT_COMPARISON_B_RV32(rs1p, rs2p, rdp, PMSLT_DB) <->
  0b1 @ 0b1010 @ 0b10 @ rs2p @ 0b1 @ rs1p @ 0b1110 @ rdp @ 0b00011011
mapping clause encdec = PEXT_COMPARISON_B_RV32(rs1p, rs2p, rdp, PMSLTU_DB) <->
  0b1 @ 0b1011 @ 0b10 @ rs2p @ 0b1 @ rs1p @ 0b1110 @ rdp @ 0b00011011
mapping clause encdec = PEXT_COMPARISON_B_RV32(rs1p, rs2p, rdp, PMIN_DB) <->
  0b1 @ 0b1100 @ 0b10 @ rs2p @ 0b1 @ rs1p @ 0b1110 @ rdp @ 0b00011011
mapping clause encdec = PEXT_COMPARISON_B_RV32(rs1p, rs2p, rdp, PMINU_DB) <->
  0b1 @ 0b1101 @ 0b10 @ rs2p @ 0b1 @ rs1p @ 0b1110 @ rdp @ 0b00011011
mapping clause encdec = PEXT_COMPARISON_B_RV32(rs1p, rs2p, rdp, PMAX_DB) <->
  0b1 @ 0b1110 @ 0b10 @ rs2p @ 0b1 @ rs1p @ 0b1110 @ rdp @ 0b00011011
mapping clause encdec = PEXT_COMPARISON_B_RV32(rs1p, rs2p, rdp, PMAXU_DB) <->
  0b1 @ 0b1111 @ 0b10 @ rs2p @ 0b1 @ rs1p @ 0b1110 @ rdp @ 0b00011011

function clause execute (PEXT_COMPARISON_B_RV32(rs1p, rs2p, rdp, op)) = {
  let rs1_val = X(rs1p @ 0b1) @ X(rs1p @ 0b0);
  let rs2_val = X(rs2p @ 0b1) @ X(rs2p @ 0b0);
  var result : bits(64) = zeros();
  foreach (i from 0 to (64 - 8) by 8) {
    let rs1_byte = slice(rs1_val, i, 8);
    let rs2_byte = slice(rs2_val, i, 8);
    result[(i+7)..i] = match op {
      PMSEQ_DB => mseq(rs1_byte, rs2_byte),
      PMSLT_DB => mslt(rs1_byte, rs2_byte),
      PMSLTU_DB => msltu(rs1_byte, rs2_byte),
      PMIN_DB => mins(rs1_byte, rs2_byte),
      PMINU_DB => minu(rs1_byte, rs2_byte),
      PMAX_DB => maxs(rs1_byte, rs2_byte),
      PMAXU_DB => maxu(rs1_byte, rs2_byte)
    };
  };
  X(rdp @ 0b1) = result[63..32];
  X(rdp @ 0b0) = result[31..0];
  RETIRE_SUCCESS
}

mapping p_comparison_b_rv32_mapping : p_comparison_b_rv32 <-> string = {
  PMSEQ_DB <-> "pmseq.db",
  PMSLT_DB <-> "pmslt.db",
  PMSLTU_DB <-> "pmsltu.db",
  PMIN_DB <-> "pmin.db",
  PMINU_DB <-> "pmin.db",
  PMAX_DB <-> "pmax.db",
  PMAXU_DB <-> "pmax.db"
}

mapping clause assembly = PEXT_COMPARISON_B_RV32(rs1p, rs2p, rdp, p_inst)
  <-> p_comparison_b_rv32_mapping(p_inst) ^ spc() ^ preg_name(rdp) ^ sep() ^ preg_name(rs1p) ^ sep() ^ preg_name(rs2p)

/* ****************************************************************** */

union clause ast = PEXT_COMPARISON_H_RV32 : (pregidx, pregidx, pregidx, p_comparison_h_rv32)

mapping clause encdec = PEXT_COMPARISON_H_RV32(rs1p, rs2p, rdp, PMSEQ_DH) <->
  0b1 @ 0b1000 @ 0b00 @ rs2p @ 0b1 @ rs1p @ 0b1110 @ rdp @ 0b00011011
mapping clause encdec = PEXT_COMPARISON_H_RV32(rs1p, rs2p, rdp, PMSLT_DH) <->
  0b1 @ 0b1010 @ 0b00 @ rs2p @ 0b1 @ rs1p @ 0b1110 @ rdp @ 0b00011011
mapping clause encdec = PEXT_COMPARISON_H_RV32(rs1p, rs2p, rdp, PMSLTU_DH) <->
  0b1 @ 0b1011 @ 0b00 @ rs2p @ 0b1 @ rs1p @ 0b1110 @ rdp @ 0b00011011
mapping clause encdec = PEXT_COMPARISON_H_RV32(rs1p, rs2p, rdp, PMIN_DH) <->
  0b1 @ 0b1100 @ 0b00 @ rs2p @ 0b1 @ rs1p @ 0b1110 @ rdp @ 0b00011011
mapping clause encdec = PEXT_COMPARISON_H_RV32(rs1p, rs2p, rdp, PMINU_DH) <->
  0b1 @ 0b1101 @ 0b00 @ rs2p @ 0b1 @ rs1p @ 0b1110 @ rdp @ 0b00011011
mapping clause encdec = PEXT_COMPARISON_H_RV32(rs1p, rs2p, rdp, PMAX_DH) <->
  0b1 @ 0b1110 @ 0b00 @ rs2p @ 0b1 @ rs1p @ 0b1110 @ rdp @ 0b00011011
mapping clause encdec = PEXT_COMPARISON_H_RV32(rs1p, rs2p, rdp, PMAXU_DH) <->
  0b1 @ 0b1111 @ 0b00 @ rs2p @ 0b1 @ rs1p @ 0b1110 @ rdp @ 0b00011011

function clause execute (PEXT_COMPARISON_H_RV32(rs1p, rs2p, rdp, op)) = {
  let rs1_val = X(rs1p @ 0b1) @ X(rs1p @ 0b0);
  let rs2_val = X(rs2p @ 0b1) @ X(rs2p @ 0b0);
  var result : bits(64) = zeros();
  foreach (i from 0 to (64 - 16) by 16) {
    let rs1_halfword = slice(rs1_val, i, 16);
    let rs2_halfword = slice(rs2_val, i, 16);
    result[(i+15)..i] = match op {
      PMSEQ_DH => mseq(rs1_halfword, rs2_halfword),
      PMSLT_DH => mslt(rs1_halfword, rs2_halfword),
      PMSLTU_DH => msltu(rs1_halfword, rs2_halfword),
      PMIN_DH => mins(rs1_halfword, rs2_halfword),
      PMINU_DH => minu(rs1_halfword, rs2_halfword),
      PMAX_DH => maxs(rs1_halfword, rs2_halfword),
      PMAXU_DH => maxu(rs1_halfword, rs2_halfword)
    };
  };
  X(rdp @ 0b1) = result[63..32];
  X(rdp @ 0b0) = result[31..0];
  RETIRE_SUCCESS
}

mapping p_comparison_h_rv32_mapping : p_comparison_h_rv32 <-> string = {
  PMSEQ_DH <-> "pmseq.dh",
  PMSLT_DH <-> "pmslt.dh",
  PMSLTU_DH <-> "pmsltu.dh",
  PMIN_DH <-> "pmin.dh",
  PMINU_DH <-> "pmin.dh",
  PMAX_DH <-> "pmax.dh",
  PMAXU_DH <-> "pmax.dh"
}

mapping clause assembly = PEXT_COMPARISON_H_RV32(rs1p, rs2p, rdp, p_inst)
  <-> p_comparison_h_rv32_mapping(p_inst) ^ spc() ^ preg_name(rdp) ^ sep() ^ preg_name(rs1p) ^ sep() ^ preg_name(rs2p)

/* ****************************************************************** */

union clause ast = PEXT_COMPARISON_W_RV32 : (pregidx, pregidx, pregidx, p_comparison_w_rv32)

mapping clause encdec = PEXT_COMPARISON_W_RV32(rs1p, rs2p, rdp, PMSEQ_DW) <->
  0b1 @ 0b1000 @ 0b01 @ rs2p @ 0b1 @ rs1p @ 0b1110 @ rdp @ 0b00011011
mapping clause encdec = PEXT_COMPARISON_W_RV32(rs1p, rs2p, rdp, PMSLT_DW) <->
  0b1 @ 0b1010 @ 0b01 @ rs2p @ 0b1 @ rs1p @ 0b1110 @ rdp @ 0b00011011
mapping clause encdec = PEXT_COMPARISON_W_RV32(rs1p, rs2p, rdp, PMSLTU_DW) <->
  0b1 @ 0b1011 @ 0b01 @ rs2p @ 0b1 @ rs1p @ 0b1110 @ rdp @ 0b00011011
mapping clause encdec = PEXT_COMPARISON_W_RV32(rs1p, rs2p, rdp, PMIN_DW) <->
  0b1 @ 0b1100 @ 0b01 @ rs2p @ 0b1 @ rs1p @ 0b1110 @ rdp @ 0b00011011
mapping clause encdec = PEXT_COMPARISON_W_RV32(rs1p, rs2p, rdp, PMINU_DW) <->
  0b1 @ 0b1101 @ 0b01 @ rs2p @ 0b1 @ rs1p @ 0b1110 @ rdp @ 0b00011011
mapping clause encdec = PEXT_COMPARISON_W_RV32(rs1p, rs2p, rdp, PMAX_DW) <->
  0b1 @ 0b1110 @ 0b01 @ rs2p @ 0b1 @ rs1p @ 0b1110 @ rdp @ 0b00011011
mapping clause encdec = PEXT_COMPARISON_W_RV32(rs1p, rs2p, rdp, PMAXU_DW) <->
  0b1 @ 0b1111 @ 0b01 @ rs2p @ 0b1 @ rs1p @ 0b1110 @ rdp @ 0b00011011

function clause execute (PEXT_COMPARISON_W_RV32(rs1p, rs2p, rdp, op)) = {
  let rs1_val = X(rs1p @ 0b1) @ X(rs1p @ 0b0);
  let rs2_val = X(rs2p @ 0b1) @ X(rs2p @ 0b0);
  var result : bits(64) = zeros();
  foreach (i from 0 to (64 - 32) by 32) {
    let rs1_word = slice(rs1_val, i, 32);
    let rs2_word = slice(rs2_val, i, 32);
    result[(i+31)..i] = match op {
      PMSEQ_DW => mseq(rs1_word, rs2_word),
      PMSLT_DW => mslt(rs1_word, rs2_word),
      PMSLTU_DW => msltu(rs1_word, rs2_word),
      PMIN_DW => mins(rs1_word, rs2_word),
      PMINU_DW => minu(rs1_word, rs2_word),
      PMAX_DW => maxs(rs1_word, rs2_word),
      PMAXU_DW => maxu(rs1_word, rs2_word)
    };
  };
  X(rdp @ 0b1) = result[63..32];
  X(rdp @ 0b0) = result[31..0];
  RETIRE_SUCCESS
}

mapping p_comparison_w_rv32_mapping : p_comparison_w_rv32 <-> string = {
  PMSEQ_DW <-> "pmseq.dw",
  PMSLT_DW <-> "pmslt.dw",
  PMSLTU_DW <-> "pmsltu.dw",
  PMIN_DW <-> "pmin.dw",
  PMINU_DW <-> "pmin.dw",
  PMAX_DW <-> "pmax.dw",
  PMAXU_DW <-> "pmax.dw"
}

mapping clause assembly = PEXT_COMPARISON_W_RV32(rs1p, rs2p, rdp, p_inst)
  <-> p_comparison_w_rv32_mapping(p_inst) ^ spc() ^ preg_name(rdp) ^ sep() ^ preg_name(rs1p) ^ sep() ^ preg_name(rs2p)
