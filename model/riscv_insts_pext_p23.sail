union clause ast = PEXT_ELEMENTARY_B_RV32 : (pregidx, pregidx, pregidx, p_elementary_b_rv32)

mapping clause encdec = PEXT_ELEMENTARY_B_RV32(rs1p, rs2p, rdp, PADD_DB) <->
  0b1 @ 0b0000 @ 0b10 @ rs2p @ 0b0 @ rs1p @ 0b0110 @ rdp @ 0b00011011
mapping clause encdec = PEXT_ELEMENTARY_B_RV32(rs1p, rs2p, rdp, PSADD_DB) <->
  0b1 @ 0b0010 @ 0b10 @ rs2p @ 0b0 @ rs1p @ 0b0110 @ rdp @ 0b00011011
mapping clause encdec = PEXT_ELEMENTARY_B_RV32(rs1p, rs2p, rdp, PAADD_DB) <->
  0b1 @ 0b0011 @ 0b10 @ rs2p @ 0b0 @ rs1p @ 0b0110 @ rdp @ 0b00011011
mapping clause encdec = PEXT_ELEMENTARY_B_RV32(rs1p, rs2p, rdp, PSADDU_DB) <->
  0b1 @ 0b0110 @ 0b10 @ rs2p @ 0b0 @ rs1p @ 0b0110 @ rdp @ 0b00011011
mapping clause encdec = PEXT_ELEMENTARY_B_RV32(rs1p, rs2p, rdp, PAADDU_DB) <->
  0b1 @ 0b0111 @ 0b10 @ rs2p @ 0b0 @ rs1p @ 0b0110 @ rdp @ 0b00011011
mapping clause encdec = PEXT_ELEMENTARY_B_RV32(rs1p, rs2p, rdp, PSUB_DB) <->
  0b1 @ 0b1000 @ 0b10 @ rs2p @ 0b0 @ rs1p @ 0b0110 @ rdp @ 0b00011011
mapping clause encdec = PEXT_ELEMENTARY_B_RV32(rs1p, rs2p, rdp, PDIF_DB) <->
  0b1 @ 0b1001 @ 0b10 @ rs2p @ 0b0 @ rs1p @ 0b0110 @ rdp @ 0b00011011
mapping clause encdec = PEXT_ELEMENTARY_B_RV32(rs1p, rs2p, rdp, PSSUB_DB) <->
  0b1 @ 0b1010 @ 0b10 @ rs2p @ 0b0 @ rs1p @ 0b0110 @ rdp @ 0b00011011
mapping clause encdec = PEXT_ELEMENTARY_B_RV32(rs1p, rs2p, rdp, PASUB_DB) <->
  0b1 @ 0b1011 @ 0b10 @ rs2p @ 0b0 @ rs1p @ 0b0110 @ rdp @ 0b00011011
mapping clause encdec = PEXT_ELEMENTARY_B_RV32(rs1p, rs2p, rdp, PDIFU_DB) <->
  0b1 @ 0b1101 @ 0b10 @ rs2p @ 0b0 @ rs1p @ 0b0110 @ rdp @ 0b00011011
mapping clause encdec = PEXT_ELEMENTARY_B_RV32(rs1p, rs2p, rdp, PSSUBU_DB) <->
  0b1 @ 0b1110 @ 0b10 @ rs2p @ 0b0 @ rs1p @ 0b0110 @ rdp @ 0b00011011
mapping clause encdec = PEXT_ELEMENTARY_B_RV32(rs1p, rs2p, rdp, PASUBU_DB) <->
  0b1 @ 0b1111 @ 0b10 @ rs2p @ 0b0 @ rs1p @ 0b0110 @ rdp @ 0b00011011

function clause execute (PEXT_ELEMENTARY_B_RV32(rs1p, rs2p, rdp, op)) = {
  let rs1_val = X(rs1p @ 0b1) @ X(rs1p @ 0b0);
  let rs2_val = X(rs2p @ 0b1) @ X(rs2p @ 0b0);
  var result : bits(64) = zeros();
  foreach (i from 0 to (64 - 8) by 8) {
    let rs1_byte = slice(rs1_val, i, 8);
    let rs2_byte = slice(rs2_val, i, 8);
    result[(i+7)..i] = match op {
      PADD_DB => rs1_byte + rs2_byte,
      PSADD_DB => sadd(rs1_byte, rs2_byte),
      PAADD_DB => aadd(rs1_byte, rs2_byte),
      PSADDU_DB => saddu(rs1_byte, rs2_byte),
      PAADDU_DB => aaddu(rs1_byte, rs2_byte),
      PSUB_DB => rs1_byte - rs2_byte,
      PDIF_DB => sabs(rs1_byte - rs2_byte),
      PSSUB_DB => ssub(rs1_byte, rs2_byte),
      PASUB_DB => asub(rs1_byte, rs2_byte),
      PDIFU_DB => abs(rs1_byte - rs2_byte),
      PSSUBU_DB => ssubu(rs1_byte, rs2_byte),
      PASUBU_DB => asubu(rs1_byte, rs2_byte)
    };
  };
  X(rdp @ 0b1) = result[63..32];
  X(rdp @ 0b0) = result[31..0];
  RETIRE_SUCCESS
}

mapping p_elementary_b_rv32_mapping : p_elementary_b_rv32 <-> string = {
  PADD_DB <-> "padd.db",
  PSADD_DB <-> "psadd.db",
  PAADD_DB <-> "paadd.db",
  PSADDU_DB <-> "psaddu.db",
  PAADDU_DB <-> "paaddu.db",
  PSUB_DB <-> "psub.db",
  PDIF_DB <-> "pdif.db",
  PSSUB_DB <-> "pssub.db",
  PASUB_DB <-> "pasub.db",
  PDIFU_DB <-> "pdifu.db",
  PSSUBU_DB <-> "pssubu.db",
  PASUBU_DB <-> "pasubu.db"
}

mapping clause assembly = PEXT_ELEMENTARY_B_RV32(rs1p, rs2p, rdp, p_inst)
  <-> p_elementary_b_rv32_mapping(p_inst) ^ spc() ^ preg_name(rdp) ^ sep() ^ preg_name(rs1p) ^ sep() ^ preg_name(rs2p)

/* ****************************************************************** */

union clause ast = PEXT_ELEMENTARY_H_RV32 : (pregidx, pregidx, pregidx, p_elementary_h_rv32)

mapping clause encdec = PEXT_ELEMENTARY_H_RV32(rs1p, rs2p, rdp, PADD_DH) <->
  0b1 @ 0b0000 @ 0b00 @ rs2p @ 0b0 @ rs1p @ 0b0110 @ rdp @ 0b00011011
mapping clause encdec = PEXT_ELEMENTARY_H_RV32(rs1p, rs2p, rdp, PSADD_DH) <->
  0b1 @ 0b0010 @ 0b00 @ rs2p @ 0b0 @ rs1p @ 0b0110 @ rdp @ 0b00011011
mapping clause encdec = PEXT_ELEMENTARY_H_RV32(rs1p, rs2p, rdp, PAADD_DH) <->
  0b1 @ 0b0011 @ 0b00 @ rs2p @ 0b0 @ rs1p @ 0b0110 @ rdp @ 0b00011011
mapping clause encdec = PEXT_ELEMENTARY_H_RV32(rs1p, rs2p, rdp, PSADDU_DH) <->
  0b1 @ 0b0110 @ 0b00 @ rs2p @ 0b0 @ rs1p @ 0b0110 @ rdp @ 0b00011011
mapping clause encdec = PEXT_ELEMENTARY_H_RV32(rs1p, rs2p, rdp, PAADDU_DH) <->
  0b1 @ 0b0111 @ 0b00 @ rs2p @ 0b0 @ rs1p @ 0b0110 @ rdp @ 0b00011011
mapping clause encdec = PEXT_ELEMENTARY_H_RV32(rs1p, rs2p, rdp, PSUB_DH) <->
  0b1 @ 0b1000 @ 0b00 @ rs2p @ 0b0 @ rs1p @ 0b0110 @ rdp @ 0b00011011
mapping clause encdec = PEXT_ELEMENTARY_H_RV32(rs1p, rs2p, rdp, PDIF_DH) <->
  0b1 @ 0b1001 @ 0b00 @ rs2p @ 0b0 @ rs1p @ 0b0110 @ rdp @ 0b00011011
mapping clause encdec = PEXT_ELEMENTARY_H_RV32(rs1p, rs2p, rdp, PSSUB_DH) <->
  0b1 @ 0b1010 @ 0b00 @ rs2p @ 0b0 @ rs1p @ 0b0110 @ rdp @ 0b00011011
mapping clause encdec = PEXT_ELEMENTARY_H_RV32(rs1p, rs2p, rdp, PASUB_DH) <->
  0b1 @ 0b1011 @ 0b00 @ rs2p @ 0b0 @ rs1p @ 0b0110 @ rdp @ 0b00011011
mapping clause encdec = PEXT_ELEMENTARY_H_RV32(rs1p, rs2p, rdp, PDIFU_DH) <->
  0b1 @ 0b1101 @ 0b00 @ rs2p @ 0b0 @ rs1p @ 0b0110 @ rdp @ 0b00011011
mapping clause encdec = PEXT_ELEMENTARY_H_RV32(rs1p, rs2p, rdp, PSSUBU_DH) <->
  0b1 @ 0b1110 @ 0b00 @ rs2p @ 0b0 @ rs1p @ 0b0110 @ rdp @ 0b00011011
mapping clause encdec = PEXT_ELEMENTARY_H_RV32(rs1p, rs2p, rdp, PASUBU_DH) <->
  0b1 @ 0b1111 @ 0b00 @ rs2p @ 0b0 @ rs1p @ 0b0110 @ rdp @ 0b00011011

function clause execute (PEXT_ELEMENTARY_H_RV32(rs1p, rs2p, rdp, op)) = {
  let rs1_val = X(rs1p @ 0b1) @ X(rs1p @ 0b0);
  let rs2_val = X(rs2p @ 0b1) @ X(rs2p @ 0b0);
  var result : bits(64) = zeros();
  foreach (i from 0 to (64 - 16) by 16) {
    let rs1_halfword = slice(rs1_val, i, 16);
    let rs2_halfword = slice(rs2_val, i, 16);
    result[(i+15)..i] = match op {
      PADD_DH => rs1_halfword + rs2_halfword,
      PSADD_DH => sadd(rs1_halfword, rs2_halfword),
      PAADD_DH => aadd(rs1_halfword, rs2_halfword),
      PSADDU_DH => saddu(rs1_halfword, rs2_halfword),
      PAADDU_DH => aaddu(rs1_halfword, rs2_halfword),
      PSUB_DH => rs1_halfword - rs2_halfword,
      PDIF_DH => sabs(rs1_halfword - rs2_halfword),
      PSSUB_DH => ssub(rs1_halfword, rs2_halfword),
      PASUB_DH => asub(rs1_halfword, rs2_halfword),
      PDIFU_DH => abs(rs1_halfword - rs2_halfword),
      PSSUBU_DH => ssubu(rs1_halfword, rs2_halfword),
      PASUBU_DH => asubu(rs1_halfword, rs2_halfword)
    };
  };
  X(rdp @ 0b1) = result[63..32];
  X(rdp @ 0b0) = result[31..0];
  RETIRE_SUCCESS
}

mapping p_elementary_h_rv32_mapping : p_elementary_h_rv32 <-> string = {
  PADD_DH <-> "padd.dh",
  PSADD_DH <-> "psadd.dh",
  PAADD_DH <-> "paadd.dh",
  PSADDU_DH <-> "psaddu.dh",
  PAADDU_DH <-> "paaddu.dh",
  PSUB_DH <-> "psub.dh",
  PDIF_DH <-> "pdif.dh",
  PSSUB_DH <-> "pssub.dh",
  PASUB_DH <-> "pasub.dh",
  PDIFU_DH <-> "pdifu.dh",
  PSSUBU_DH <-> "pssubu.dh",
  PASUBU_DH <-> "pasubu.dh"
}

mapping clause assembly = PEXT_ELEMENTARY_H_RV32(rs1p, rs2p, rdp, p_inst)
  <-> p_elementary_h_rv32_mapping(p_inst) ^ spc() ^ preg_name(rdp) ^ sep() ^ preg_name(rs1p) ^ sep() ^ preg_name(rs2p)

/* ****************************************************************** */

union clause ast = PEXT_ELEMENTARY_W_RV32 : (pregidx, pregidx, pregidx, p_elementary_w_rv32)

mapping clause encdec = PEXT_ELEMENTARY_W_RV32(rs1p, rs2p, rdp, PADD_DW) <->
  0b1 @ 0b0000 @ 0b01 @ rs2p @ 0b0 @ rs1p @ 0b0110 @ rdp @ 0b00011011
mapping clause encdec = PEXT_ELEMENTARY_W_RV32(rs1p, rs2p, rdp, PSADD_DW) <->
  0b1 @ 0b0010 @ 0b01 @ rs2p @ 0b0 @ rs1p @ 0b0110 @ rdp @ 0b00011011
mapping clause encdec = PEXT_ELEMENTARY_W_RV32(rs1p, rs2p, rdp, PAADD_DW) <->
  0b1 @ 0b0011 @ 0b01 @ rs2p @ 0b0 @ rs1p @ 0b0110 @ rdp @ 0b00011011
mapping clause encdec = PEXT_ELEMENTARY_W_RV32(rs1p, rs2p, rdp, PSADDU_DW) <->
  0b1 @ 0b0110 @ 0b01 @ rs2p @ 0b0 @ rs1p @ 0b0110 @ rdp @ 0b00011011
mapping clause encdec = PEXT_ELEMENTARY_W_RV32(rs1p, rs2p, rdp, PAADDU_DW) <->
  0b1 @ 0b0111 @ 0b01 @ rs2p @ 0b0 @ rs1p @ 0b0110 @ rdp @ 0b00011011
mapping clause encdec = PEXT_ELEMENTARY_W_RV32(rs1p, rs2p, rdp, PSUB_DW) <->
  0b1 @ 0b1000 @ 0b01 @ rs2p @ 0b0 @ rs1p @ 0b0110 @ rdp @ 0b00011011
mapping clause encdec = PEXT_ELEMENTARY_W_RV32(rs1p, rs2p, rdp, PSSUB_DW) <->
  0b1 @ 0b1010 @ 0b01 @ rs2p @ 0b0 @ rs1p @ 0b0110 @ rdp @ 0b00011011
mapping clause encdec = PEXT_ELEMENTARY_W_RV32(rs1p, rs2p, rdp, PASUB_DW) <->
  0b1 @ 0b1011 @ 0b01 @ rs2p @ 0b0 @ rs1p @ 0b0110 @ rdp @ 0b00011011
mapping clause encdec = PEXT_ELEMENTARY_W_RV32(rs1p, rs2p, rdp, PSSUBU_DW) <->
  0b1 @ 0b1110 @ 0b01 @ rs2p @ 0b0 @ rs1p @ 0b0110 @ rdp @ 0b00011011
mapping clause encdec = PEXT_ELEMENTARY_W_RV32(rs1p, rs2p, rdp, PASUBU_DW) <->
  0b1 @ 0b1111 @ 0b01 @ rs2p @ 0b0 @ rs1p @ 0b0110 @ rdp @ 0b00011011

function clause execute (PEXT_ELEMENTARY_W_RV32(rs1p, rs2p, rdp, op)) = {
  let rs1_val = X(rs1p @ 0b1) @ X(rs1p @ 0b0);
  let rs2_val = X(rs2p @ 0b1) @ X(rs2p @ 0b0);
  var result : bits(64) = zeros();
  foreach (i from 0 to (64 - 32) by 32) {
    let rs1_word = slice(rs1_val, i, 32);
    let rs2_word = slice(rs2_val, i, 32);
    result[(i+31)..i] = match op {
      PADD_DW => rs1_word + rs2_word,
      PSADD_DW => sadd(rs1_word, rs2_word),
      PAADD_DW => aadd(rs1_word, rs2_word),
      PSADDU_DW => saddu(rs1_word, rs2_word),
      PAADDU_DW => aaddu(rs1_word, rs2_word),
      PSUB_DW => rs1_word - rs2_word,
      PSSUB_DW => ssub(rs1_word, rs2_word),
      PASUB_DW => asub(rs1_word, rs2_word),
      PSSUBU_DW => ssubu(rs1_word, rs2_word),
      PASUBU_DW => asubu(rs1_word, rs2_word)
    };
  };
  X(rdp @ 0b1) = result[63..32];
  X(rdp @ 0b0) = result[31..0];
  RETIRE_SUCCESS
}

mapping p_elementary_w_rv32_mapping : p_elementary_w_rv32 <-> string = {
  PADD_DW <-> "padd.dw",
  PSADD_DW <-> "psadd.dw",
  PAADD_DW <-> "paadd.dw",
  PSADDU_DW <-> "psaddu.dw",
  PAADDU_DW <-> "paaddu.dw",
  PSUB_DW <-> "psub.dw",
  PSSUB_DW <-> "pssub.dw",
  PASUB_DW <-> "pasub.dw",
  PSSUBU_DW <-> "pssubu.dw",
  PASUBU_DW <-> "pasubu.dw"
}

mapping clause assembly = PEXT_ELEMENTARY_W_RV32(rs1p, rs2p, rdp, p_inst)
  <-> p_elementary_w_rv32_mapping(p_inst) ^ spc() ^ preg_name(rdp) ^ sep() ^ preg_name(rs1p) ^ sep() ^ preg_name(rs2p)

/* ****************************************************************** */

union clause ast = PEXT_ELEMENTARY_RV32 : (pregidx, pregidx, pregidx, p_elementary_rv32)

mapping clause encdec = PEXT_ELEMENTARY_RV32(rs1p, rs2p, rdp, ADDD) <->
  0b1 @ 0b0000 @ 0b11 @ rs2p @ 0b0 @ rs1p @ 0b0110 @ rdp @ 0b00011011
mapping clause encdec = PEXT_ELEMENTARY_RV32(rs1p, rs2p, rdp, SUBD) <->
  0b1 @ 0b1000 @ 0b11 @ rs2p @ 0b0 @ rs1p @ 0b0110 @ rdp @ 0b00011011

function clause execute (PEXT_ELEMENTARY_RV32(rs1p, rs2p, rdp, op)) = {
  let rs1_val = X(rs1p @ 0b1) @ X(rs1p @ 0b0);
  let rs2_val = X(rs2p @ 0b1) @ X(rs2p @ 0b0);
  var result : bits(64) = zeros();
  result = match op {
    ADDD => rs1_val + rs2_val,
    SUBD => rs1_val - rs2_val
  };
  X(rdp @ 0b1) = result[63..32];
  X(rdp @ 0b0) = result[31..0];
  RETIRE_SUCCESS
}

mapping p_elementary_rv32_mapping : p_elementary_rv32 <-> string = {
  ADDD <-> "addd",
  SUBD <-> "subd"
}

mapping clause assembly = PEXT_ELEMENTARY_RV32(rs1p, rs2p, rdp, p_inst)
  <-> p_elementary_rv32_mapping(p_inst) ^ spc() ^ preg_name(rdp) ^ sep() ^ preg_name(rs1p) ^ sep() ^ preg_name(rs2p)

/* ****************************************************************** */

union clause ast = PEXT_SH1ADD_RV32 : (pregidx, pregidx, pregidx, p_sh1add_rv32)

mapping clause encdec = PEXT_SH1ADD_RV32(rs1p, rs2p, rdp, PSH1ADD_DH) <->
  0b1 @ 0b010 @ 0b0 @ 0b00 @ rs2p @ 0b1 @ rs1p @ 0b0110 @ rdp @ 0b00011011
mapping clause encdec = PEXT_SH1ADD_RV32(rs1p, rs2p, rdp, PSSH1SADD_DH) <->
  0b1 @ 0b011 @ 0b0 @ 0b00 @ rs2p @ 0b1 @ rs1p @ 0b0110 @ rdp @ 0b00011011
mapping clause encdec = PEXT_SH1ADD_RV32(rs1p, rs2p, rdp, PSH1ADD_DW) <->
  0b1 @ 0b010 @ 0b0 @ 0b01 @ rs2p @ 0b1 @ rs1p @ 0b0110 @ rdp @ 0b00011011
mapping clause encdec = PEXT_SH1ADD_RV32(rs1p, rs2p, rdp, PSSH1SADD_DW) <->
  0b1 @ 0b011 @ 0b0 @ 0b01 @ rs2p @ 0b1 @ rs1p @ 0b0110 @ rdp @ 0b00011011

function clause execute (PEXT_SH1ADD_RV32(rs1p, rs2p, rdp, op)) = {
  let rs1_val = X(rs1p @ 0b1) @ X(rs1p @ 0b0);
  let rs2_val = X(rs2p @ 0b1) @ X(rs2p @ 0b0);
  var result : bits(64) = zeros();
  match op {
    PSH1ADD_DH => {
      foreach (i from 0 to (64 - 16) by 16) {
        result[(i+15)..i] = shift_left_logic(rs1_val[(i+15)..i], 0x01) + rs2_val[(i+15)..i];
      };
    },
    PSSH1SADD_DH => {
      foreach (i from 0 to (64 - 16) by 16) {
        result[(i+15)..i] = sadd(sat_shift_left_arith(rs1_val[(i+15)..i], 0x01), rs2_val[(i+15)..i]);
      };
    },
    PSH1ADD_DW => {
      foreach (i from 0 to (64 - 32) by 32) {
        result[(i+31)..i] = shift_left_logic(rs1_val[(i+31)..i], 0x01) + rs2_val[(i+31)..i];
      };
    },
    PSSH1SADD_DW => {
      foreach (i from 0 to (64 - 32) by 32) {
        result[(i+31)..i] = sadd(sat_shift_left_arith(rs1_val[(i+31)..i], 0x01), rs2_val[(i+31)..i]);
      };
    },
  };
  X(rdp @ 0b1) = result[63..32];
  X(rdp @ 0b0) = result[31..0];
  RETIRE_SUCCESS
}

mapping p_sh1add_rv32_mapping : p_sh1add_rv32 <-> string = {
  PSH1ADD_DH <-> "psh1add.dh",
  PSSH1SADD_DH <-> "pssh1sadd.dh",
  PSH1ADD_DW <-> "psh1add.dw",
  PSSH1SADD_DW <-> "pssh1sadd.dw"
}

mapping clause assembly = PEXT_SH1ADD_RV32(rs1p, rs2p, rdp, p_inst)
  <-> p_sh1add_rv32_mapping(p_inst) ^ spc() ^ preg_name(rdp) ^ sep() ^ preg_name(rs1p) ^ sep() ^ preg_name(rs2p)
