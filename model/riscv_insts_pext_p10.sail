union clause ast = PEXT_ELEMENTARY_B : (regidx, regidx, regidx, p_elementary_b)

mapping clause encdec = PEXT_ELEMENTARY_B(rs1, rs2, rd, PADD_B) <->
  0b1 @ 0b0000 @ 0b10 @ rs2 @ rs1 @ 0b000 @ rd @ 0b0111011
mapping clause encdec = PEXT_ELEMENTARY_B(rs1, rs2, rd, PSADD_B) <->
  0b1 @ 0b0010 @ 0b10 @ rs2 @ rs1 @ 0b000 @ rd @ 0b0111011
mapping clause encdec = PEXT_ELEMENTARY_B(rs1, rs2, rd, PAADD_B) <->
  0b1 @ 0b0011 @ 0b10 @ rs2 @ rs1 @ 0b000 @ rd @ 0b0111011
mapping clause encdec = PEXT_ELEMENTARY_B(rs1, rs2, rd, PSADDU_B) <->
  0b1 @ 0b0110 @ 0b10 @ rs2 @ rs1 @ 0b000 @ rd @ 0b0111011
mapping clause encdec = PEXT_ELEMENTARY_B(rs1, rs2, rd, PAADDU_B) <->
  0b1 @ 0b0010 @ 0b10 @ rs2 @ rs1 @ 0b000 @ rd @ 0b0111011
mapping clause encdec = PEXT_ELEMENTARY_B(rs1, rs2, rd, PSUB_B) <->
  0b1 @ 0b1000 @ 0b10 @ rs2 @ rs1 @ 0b000 @ rd @ 0b0111011
mapping clause encdec = PEXT_ELEMENTARY_B(rs1, rs2, rd, PDIF_B) <->
  0b1 @ 0b1001 @ 0b10 @ rs2 @ rs1 @ 0b000 @ rd @ 0b0111011
mapping clause encdec = PEXT_ELEMENTARY_B(rs1, rs2, rd, PSSUB_B) <->
  0b1 @ 0b1010 @ 0b10 @ rs2 @ rs1 @ 0b000 @ rd @ 0b0111011
mapping clause encdec = PEXT_ELEMENTARY_B(rs1, rs2, rd, PASUB_B) <->
  0b1 @ 0b1011 @ 0b10 @ rs2 @ rs1 @ 0b000 @ rd @ 0b0111011
mapping clause encdec = PEXT_ELEMENTARY_B(rs1, rs2, rd, PDIFU_B) <->
  0b1 @ 0b1101 @ 0b10 @ rs2 @ rs1 @ 0b000 @ rd @ 0b0111011
mapping clause encdec = PEXT_ELEMENTARY_B(rs1, rs2, rd, PSSUBU_B) <->
  0b1 @ 0b1110 @ 0b10 @ rs2 @ rs1 @ 0b000 @ rd @ 0b0111011
mapping clause encdec = PEXT_ELEMENTARY_B(rs1, rs2, rd, PASUBU_B) <->
  0b1 @ 0b1111 @ 0b10 @ rs2 @ rs1 @ 0b000 @ rd @ 0b0111011

function clause execute (PEXT_ELEMENTARY_B(rs1, rs2, rd, op)) = {
  let rs1_val = X(rs1);
  let rs2_val = X(rs2);
  var result : xlenbits = zeros();
  foreach (i from 0 to (sizeof(xlen) - 8) by 8) {
    let rs1_byte = slice(rs1_val, i, 8);
    let rs2_byte = slice(rs2_val, i, 8);
    result[(i+7)..i] = match op {
      PADD_B => rs1_byte + rs2_byte,
      PSADD_B => sadd(rs1_byte, rs2_byte),
      PAADD_B => aadd(rs1_byte, rs2_byte),
      PSADDU_B => saddu(rs1_byte, rs2_byte),
      PAADDU_B => aaddu(rs1_byte, rs2_byte),
      PSUB_B => rs1_byte - rs2_byte,
      PDIF_B => sabs(rs1_byte - rs2_byte),
      PSSUB_B => ssub(rs1_byte, rs2_byte),
      PASUB_B => asub(rs1_byte, rs2_byte),
      PDIFU_B => abs(rs1_byte - rs2_byte),
      PSSUBU_B => ssubu(rs1_byte, rs2_byte),
      PASUBU_B => asubu(rs1_byte, rs2_byte)
    };
  };
  X(rd) = result;
  RETIRE_SUCCESS
}

mapping p_elementary_b_mapping : p_elementary_b <-> string = {
  PADD_B <-> "padd.b",
  PSADD_B <-> "psadd.b",
  PAADD_B <-> "paadd.b",
  PSADDU_B <-> "psaddu.b",
  PAADDU_B <-> "paaddu.b",
  PSUB_B <-> "psub.b",
  PDIF_B <-> "pdif.b",
  PSSUB_B <-> "pssub.b",
  PASUB_B <-> "pasub.b",
  PDIFU_B <-> "pdifu.b",
  PSSUBU_B <-> "pssubu.b",
  PASUBU_B <-> "pasubu.b"
}

mapping clause assembly = PEXT_ELEMENTARY_B(rs1, rs2, rd, p_inst)
  <-> p_elementary_b_mapping(p_inst) ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2) // TODO: The order is probably correct, but we still have to check.

/* ****************************************************************** */

union clause ast = PEXT_ELEMENTARY_H : (regidx, regidx, regidx, p_elementary_h)

mapping clause encdec = PEXT_ELEMENTARY_H(rs1, rs2, rd, PADD_H) <->
  0b1 @ 0b0000 @ 0b00 @ rs2 @ rs1 @ 0b000 @ rd @ 0b0111011
mapping clause encdec = PEXT_ELEMENTARY_H(rs1, rs2, rd, PSADD_H) <->
  0b1 @ 0b0010 @ 0b00 @ rs2 @ rs1 @ 0b000 @ rd @ 0b0111011
mapping clause encdec = PEXT_ELEMENTARY_H(rs1, rs2, rd, PAADD_H) <->
  0b1 @ 0b0011 @ 0b00 @ rs2 @ rs1 @ 0b000 @ rd @ 0b0111011
mapping clause encdec = PEXT_ELEMENTARY_H(rs1, rs2, rd, PSADDU_H) <->
  0b1 @ 0b0110 @ 0b00 @ rs2 @ rs1 @ 0b000 @ rd @ 0b0111011
mapping clause encdec = PEXT_ELEMENTARY_H(rs1, rs2, rd, PAADDU_H) <->
  0b1 @ 0b0010 @ 0b00 @ rs2 @ rs1 @ 0b000 @ rd @ 0b0111011
mapping clause encdec = PEXT_ELEMENTARY_H(rs1, rs2, rd, PSUB_H) <->
  0b1 @ 0b1000 @ 0b00 @ rs2 @ rs1 @ 0b000 @ rd @ 0b0111011
mapping clause encdec = PEXT_ELEMENTARY_H(rs1, rs2, rd, PDIF_H) <->
  0b1 @ 0b1001 @ 0b00 @ rs2 @ rs1 @ 0b000 @ rd @ 0b0111011
mapping clause encdec = PEXT_ELEMENTARY_H(rs1, rs2, rd, PSSUB_H) <->
  0b1 @ 0b1010 @ 0b00 @ rs2 @ rs1 @ 0b000 @ rd @ 0b0111011
mapping clause encdec = PEXT_ELEMENTARY_H(rs1, rs2, rd, PASUB_H) <->
  0b1 @ 0b1011 @ 0b00 @ rs2 @ rs1 @ 0b000 @ rd @ 0b0111011
mapping clause encdec = PEXT_ELEMENTARY_H(rs1, rs2, rd, PDIFU_H) <->
  0b1 @ 0b1101 @ 0b00 @ rs2 @ rs1 @ 0b000 @ rd @ 0b0111011
mapping clause encdec = PEXT_ELEMENTARY_H(rs1, rs2, rd, PSSUBU_H) <->
  0b1 @ 0b1110 @ 0b00 @ rs2 @ rs1 @ 0b000 @ rd @ 0b0111011
mapping clause encdec = PEXT_ELEMENTARY_H(rs1, rs2, rd, PASUBU_H) <->
  0b1 @ 0b1111 @ 0b00 @ rs2 @ rs1 @ 0b000 @ rd @ 0b0111011

function clause execute (PEXT_ELEMENTARY_H(rs1, rs2, rd, op)) = {
  let rs1_val = X(rs1);
  let rs2_val = X(rs2);
  var result : xlenbits = zeros();
  foreach (i from 0 to (sizeof(xlen) - 16) by 16) {
    let rs1_halfword = slice(rs1_val, i, 16);
    let rs2_halfword = slice(rs2_val, i, 16);
    result[(i+15)..i] = match op {
      PADD_H => rs1_halfword + rs2_halfword,
      PSADD_H => sadd(rs1_halfword, rs2_halfword),
      PAADD_H => aadd(rs1_halfword, rs2_halfword),
      PSADDU_H => saddu(rs1_halfword, rs2_halfword),
      PAADDU_H => aaddu(rs1_halfword, rs2_halfword),
      PSUB_H => rs1_halfword - rs2_halfword,
      PDIF_H => sabs(rs1_halfword - rs2_halfword),
      PSSUB_H => ssub(rs1_halfword, rs2_halfword),
      PASUB_H => asub(rs1_halfword, rs2_halfword),
      PDIFU_H => abs(rs1_halfword - rs2_halfword),
      PSSUBU_H => ssubu(rs1_halfword, rs2_halfword),
      PASUBU_H => asubu(rs1_halfword, rs2_halfword)
    };
  };
  X(rd) = result;
  RETIRE_SUCCESS
}

mapping p_elementary_h_mapping : p_elementary_h <-> string = {
  PADD_H <-> "padd.h",
  PSADD_H <-> "psadd.h",
  PAADD_H <-> "paadd.h",
  PSADDU_H <-> "psaddu.h",
  PAADDU_H <-> "paaddu.h",
  PSUB_H <-> "psub.h",
  PDIF_H <-> "pdif.h",
  PSSUB_H <-> "pssub.h",
  PASUB_H <-> "pasub.h",
  PDIFU_H <-> "pdifu.h",
  PSSUBU_H <-> "pssubu.h",
  PASUBU_H <-> "pasubu.h"
}

mapping clause assembly = PEXT_ELEMENTARY_H(rs1, rs2, rd, p_inst)
  <-> p_elementary_h_mapping(p_inst) ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2) // TODO: The order is probably correct, but we still have to check.

/* ****************************************************************** */

union clause ast = PEXT_ELEMENTARY_W : (regidx, regidx, regidx, p_elementary_w)

mapping clause encdec = PEXT_ELEMENTARY_W(rs1, rs2, rd, PADD_W) if sizeof(xlen) == 64 <->
  0b1 @ 0b0000 @ 0b01 @ rs2 @ rs1 @ 0b000 @ rd @ 0b0111011 if sizeof(xlen) == 64
mapping clause encdec = PEXT_ELEMENTARY_W(rs1, rs2, rd, PSADD_W) if sizeof(xlen) == 64 <->
  0b1 @ 0b0010 @ 0b01 @ rs2 @ rs1 @ 0b000 @ rd @ 0b0111011 if sizeof(xlen) == 64
mapping clause encdec = PEXT_ELEMENTARY_W(rs1, rs2, rd, PAADD_W) if sizeof(xlen) == 64 <->
  0b1 @ 0b0011 @ 0b01 @ rs2 @ rs1 @ 0b000 @ rd @ 0b0111011 if sizeof(xlen) == 64
mapping clause encdec = PEXT_ELEMENTARY_W(rs1, rs2, rd, PSADDU_W) if sizeof(xlen) == 64 <->
  0b1 @ 0b0110 @ 0b01 @ rs2 @ rs1 @ 0b000 @ rd @ 0b0111011 if sizeof(xlen) == 64
mapping clause encdec = PEXT_ELEMENTARY_W(rs1, rs2, rd, PAADDU_W) if sizeof(xlen) == 64 <->
  0b1 @ 0b0010 @ 0b01 @ rs2 @ rs1 @ 0b000 @ rd @ 0b0111011 if sizeof(xlen) == 64
mapping clause encdec = PEXT_ELEMENTARY_W(rs1, rs2, rd, PSUB_W) if sizeof(xlen) == 64 <->
  0b1 @ 0b1000 @ 0b01 @ rs2 @ rs1 @ 0b000 @ rd @ 0b0111011 if sizeof(xlen) == 64
mapping clause encdec = PEXT_ELEMENTARY_W(rs1, rs2, rd, PSSUB_W) if sizeof(xlen) == 64 <->
  0b1 @ 0b1010 @ 0b01 @ rs2 @ rs1 @ 0b000 @ rd @ 0b0111011 if sizeof(xlen) == 64
mapping clause encdec = PEXT_ELEMENTARY_W(rs1, rs2, rd, PASUB_W) if sizeof(xlen) == 64 <->
  0b1 @ 0b1011 @ 0b01 @ rs2 @ rs1 @ 0b000 @ rd @ 0b0111011 if sizeof(xlen) == 64
mapping clause encdec = PEXT_ELEMENTARY_W(rs1, rs2, rd, PSSUBU_W) if sizeof(xlen) == 64 <->
  0b1 @ 0b1110 @ 0b01 @ rs2 @ rs1 @ 0b000 @ rd @ 0b0111011 if sizeof(xlen) == 64
mapping clause encdec = PEXT_ELEMENTARY_W(rs1, rs2, rd, PASUBU_W) if sizeof(xlen) == 64 <->
  0b1 @ 0b1111 @ 0b01 @ rs2 @ rs1 @ 0b000 @ rd @ 0b0111011 if sizeof(xlen) == 64

function clause execute (PEXT_ELEMENTARY_W(rs1, rs2, rd, op)) = {
  let rs1_val = X(rs1);
  let rs2_val = X(rs2);
  var result : xlenbits = zeros();
  foreach (i from 0 to (sizeof(xlen) - 32) by 32) {
    let rs1_word = slice(rs1_val, i, 32);
    let rs2_word = slice(rs2_val, i, 32);
    result[(i+31)..i] = match op {
      PADD_W => rs1_word + rs2_word,
      PSADD_W => sadd(rs1_word, rs2_word),
      PAADD_W => aadd(rs1_word, rs2_word),
      PSADDU_W => saddu(rs1_word, rs2_word),
      PAADDU_W => aaddu(rs1_word, rs2_word),
      PSUB_W => rs1_word - rs2_word,
      PSSUB_W => ssub(rs1_word, rs2_word),
      PASUB_W => asub(rs1_word, rs2_word),
      PSSUBU_W => ssubu(rs1_word, rs2_word),
      PASUBU_W => asubu(rs1_word, rs2_word)
    };
  };
  X(rd) = result;
  RETIRE_SUCCESS
}

mapping p_elementary_w_mapping : p_elementary_w <-> string = {
  PADD_W <-> "padd.w",
  PSADD_W <-> "psadd.w",
  PAADD_W <-> "paadd.w",
  PSADDU_W <-> "psaddu.w",
  PAADDU_W <-> "paaddu.w",
  PSUB_W <-> "psub.w",
  PSSUB_W <-> "pssub.w",
  PASUB_W <-> "pasub.w",
  PSSUBU_W <-> "pssubu.w",
  PASUBU_W <-> "pasubu.w"
}

mapping clause assembly = PEXT_ELEMENTARY_W(rs1, rs2, rd, p_inst)
  <-> p_elementary_w_mapping(p_inst) ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2) // TODO: The order is probably correct, but we still have to check.

/* ****************************************************************** */

union clause ast = PEXT_ELEMENTARY : (regidx, regidx, regidx, p_elementary)

mapping clause encdec = PEXT_ELEMENTARY(rs1, rs2, rd, SADD) if sizeof(xlen) == 32 <->
  0b1 @ 0b0010 @ 0b01 @ rs2 @ rs1 @ 0b000 @ rd @ 0b0111011 if sizeof(xlen) == 32
mapping clause encdec = PEXT_ELEMENTARY(rs1, rs2, rd, AADD) if sizeof(xlen) == 32 <->
  0b1 @ 0b0011 @ 0b01 @ rs2 @ rs1 @ 0b000 @ rd @ 0b0111011 if sizeof(xlen) == 32
mapping clause encdec = PEXT_ELEMENTARY(rs1, rs2, rd, SADDU) if sizeof(xlen) == 32 <->
  0b1 @ 0b0110 @ 0b01 @ rs2 @ rs1 @ 0b000 @ rd @ 0b0111011 if sizeof(xlen) == 32
mapping clause encdec = PEXT_ELEMENTARY(rs1, rs2, rd, AADDU) if sizeof(xlen) == 32 <->
  0b1 @ 0b0010 @ 0b01 @ rs2 @ rs1 @ 0b000 @ rd @ 0b0111011 if sizeof(xlen) == 32
mapping clause encdec = PEXT_ELEMENTARY(rs1, rs2, rd, SSUB) if sizeof(xlen) == 32 <->
  0b1 @ 0b1010 @ 0b01 @ rs2 @ rs1 @ 0b000 @ rd @ 0b0111011 if sizeof(xlen) == 32
mapping clause encdec = PEXT_ELEMENTARY(rs1, rs2, rd, ASUB) if sizeof(xlen) == 32 <->
  0b1 @ 0b1011 @ 0b01 @ rs2 @ rs1 @ 0b000 @ rd @ 0b0111011 if sizeof(xlen) == 32
mapping clause encdec = PEXT_ELEMENTARY(rs1, rs2, rd, SSUBU) if sizeof(xlen) == 32 <->
  0b1 @ 0b1110 @ 0b01 @ rs2 @ rs1 @ 0b000 @ rd @ 0b0111011 if sizeof(xlen) == 32
mapping clause encdec = PEXT_ELEMENTARY(rs1, rs2, rd, ASUBU) if sizeof(xlen) == 32 <->
  0b1 @ 0b1111 @ 0b01 @ rs2 @ rs1 @ 0b000 @ rd @ 0b0111011 if sizeof(xlen) == 32

function clause execute (PEXT_ELEMENTARY(rs1, rs2, rd, op)) = {
  let rs1_val = X(rs1);
  let rs2_val = X(rs2);
  var result : xlenbits = zeros();
  result = match op {
    SADD => sadd(rs1_val, rs2_val),
    AADD => aadd(rs1_val, rs2_val),
    SADDU => saddu(rs1_val, rs2_val),
    AADDU => aaddu(rs1_val, rs2_val),
    SSUB => ssub(rs1_val, rs2_val),
    ASUB => asub(rs1_val, rs2_val),
    SSUBU => ssubu(rs1_val, rs2_val),
    ASUBU => asubu(rs1_val, rs2_val)
  };
  X(rd) = result;
  RETIRE_SUCCESS
}

mapping p_elementary_mapping : p_elementary <-> string = {
  SADD <-> "sadd",
  AADD <-> "aadd",
  SADDU <-> "saddu",
  AADDU <-> "aaddu",
  SSUB <-> "ssub",
  ASUB <-> "asub",
  SSUBU <-> "ssubu",
  ASUBU <-> "asubu"
}

mapping clause assembly = PEXT_ELEMENTARY(rs1, rs2, rd, p_inst)
  <-> p_elementary_mapping(p_inst) ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2) // TODO: The order is probably correct, but we still have to check.
  