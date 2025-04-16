union clause ast = PEXT_WIDENING_SHIFT_LEFT_B : (regidx, regidx, pregidx, p_widening_shift_left_b)

mapping clause encdec = PEXT_WIDENING_SHIFT_LEFT_B(rs1, rs2, rdp, PWSLL_BS) <->
  0b0 @ 0b000 @ 0b1 @ 0b00 @ rs2 @ rs1 @ 0b010 @ rdp @ 0b00011011
mapping clause encdec = PEXT_WIDENING_SHIFT_LEFT_B(rs1, rs2, rdp, PWSLA_BS) <->
  0b0 @ 0b100 @ 0b1 @ 0b00 @ rs2 @ rs1 @ 0b010 @ rdp @ 0b00011011

function clause execute (PEXT_WIDENING_SHIFT_LEFT_B(rs1, rs2, rdp, op)) = {
  if rdp == 0x0 then RETIRE_SUCCESS else {
  let rs1_val = X(rs1);
  let sa : bits(8) = X(rs2)[7..0];
  var result : bits(64) = zeros();
  foreach (i from 0 to (sizeof(xlen) - 8) by 8) {
    result[(2*i+15)..(2*i)] = match op {
      PWSLL_BS => shift_left_logic(0x00 @ rs1_val[(i+7)..i], sa),
      PWSLA_BS => shift_left_logic(sign_extend(16, rs1_val[(i+7)..i]), sa)
    };
  };
  X(rdp @ 0b1) = result[63..32];
  X(rdp @ 0b0) = result[31..0];
  RETIRE_SUCCESS
}}

mapping p_widening_shift_left_b_mapping : p_widening_shift_left_b <-> string = {
  PWSLL_BS <-> "pwsll.bs",
  PWSLA_BS <-> "pwsla.bs"
}

mapping clause assembly = PEXT_WIDENING_SHIFT_LEFT_B(rs1, rs2, rdp, p_inst)
  <-> p_widening_shift_left_b_mapping(p_inst) ^ spc() ^ preg_name(rdp) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)

/* ****************************************************************** */

union clause ast = PEXT_WIDENING_SHIFT_LEFT_H : (regidx, regidx, pregidx, p_widening_shift_left_h)

mapping clause encdec = PEXT_WIDENING_SHIFT_LEFT_H(rs1, rs2, rdp, PWSLL_HS) <->
  0b0 @ 0b000 @ 0b1 @ 0b01 @ rs2 @ rs1 @ 0b010 @ rdp @ 0b00011011
mapping clause encdec = PEXT_WIDENING_SHIFT_LEFT_H(rs1, rs2, rdp, PWSLA_HS) <->
  0b0 @ 0b100 @ 0b1 @ 0b01 @ rs2 @ rs1 @ 0b010 @ rdp @ 0b00011011

function clause execute (PEXT_WIDENING_SHIFT_LEFT_H(rs1, rs2, rdp, op)) = {
  if rdp == 0x0 then RETIRE_SUCCESS else {
  let rs1_val = X(rs1);
  let sa : bits(8) = X(rs2)[7..0];
  var result : bits(64) = zeros();
  foreach (i from 0 to (sizeof(xlen) - 16) by 16) {
    result[(2*i+31)..(2*i)] = match op {
      PWSLL_HS => shift_left_logic(0x0000 @ rs1_val[(i+15)..i], sa),
      PWSLA_HS => shift_left_logic(sign_extend(32, rs1_val[(i+15)..i]), sa)
    };
  };
  X(rdp @ 0b1) = result[63..32];
  X(rdp @ 0b0) = result[31..0];
  RETIRE_SUCCESS
}}

mapping p_widening_shift_left_h_mapping : p_widening_shift_left_h <-> string = {
  PWSLL_HS <-> "pwsll.hs",
  PWSLA_HS <-> "pwsla.hs"
}

mapping clause assembly = PEXT_WIDENING_SHIFT_LEFT_H(rs1, rs2, rdp, p_inst)
  <-> p_widening_shift_left_h_mapping(p_inst) ^ spc() ^ preg_name(rdp) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)

/* ****************************************************************** */

union clause ast = PEXT_WIDENING_SHIFT_LEFT_W : (regidx, regidx, pregidx, p_widening_shift_left_w)

mapping clause encdec = PEXT_WIDENING_SHIFT_LEFT_W(rs1, rs2, rdp, WSLL) <->
  0b0 @ 0b000 @ 0b1 @ 0b11 @ rs2 @ rs1 @ 0b010 @ rdp @ 0b00011011
mapping clause encdec = PEXT_WIDENING_SHIFT_LEFT_W(rs1, rs2, rdp, WSLA) <->
  0b0 @ 0b100 @ 0b1 @ 0b11 @ rs2 @ rs1 @ 0b010 @ rdp @ 0b00011011

function clause execute (PEXT_WIDENING_SHIFT_LEFT_W(rs1, rs2, rdp, op)) = {
  if rdp == 0x0 then RETIRE_SUCCESS else {
  let rs1_val = X(rs1);
  let sa : bits(8) = X(rs2)[7..0];
  var result : bits(64) = zeros();
  result = match op {
    WSLL => shift_left_logic(0x00000000 @ rs1_val, sa),
    WSLA => shift_left_logic(sign_extend(64, rs1_val[31..0]), sa)
  };
  X(rdp @ 0b1) = result[63..32];
  X(rdp @ 0b0) = result[31..0];
  RETIRE_SUCCESS
}}

mapping p_widening_shift_left_w_mapping : p_widening_shift_left_w <-> string = {
  WSLL <-> "wsll",
  WSLA <-> "wsla"
}

mapping clause assembly = PEXT_WIDENING_SHIFT_LEFT_W(rs1, rs2, rdp, p_inst)
  <-> p_widening_shift_left_w_mapping(p_inst) ^ spc() ^ preg_name(rdp) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)

/* ****************************************************************** */

union clause ast = PEXT_WIDENING_ZIP : (regidx, regidx, pregidx, p_widening_zip)

mapping clause encdec = PEXT_WIDENING_ZIP(rs1, rs2, rdp, WZIP8P) <->
  0b0 @ 0b111 @ 0b1 @ 0b00 @ rs2 @ rs1 @ 0b010 @ rdp @ 0b00011011
mapping clause encdec = PEXT_WIDENING_ZIP(rs1, rs2, rdp, WZIP16P) <->
  0b0 @ 0b111 @ 0b1 @ 0b01 @ rs2 @ rs1 @ 0b010 @ rdp @ 0b00011011

function clause execute (PEXT_WIDENING_ZIP(rs1, rs2, rdp, op)) = {
  if rdp == 0x0 then RETIRE_SUCCESS else {
  let rs1_val = X(rs1);
  let rs2_val = X(rs2);
  var result : bits(64) = zeros();
  result = match op {
    WZIP8P => rs2_val[31..24] @ rs1_val[31..24] @ rs2_val[23..16] @ rs1_val[23..16]
                 @ rs2_val[15..8] @ rs1_val[15..8] @ rs2_val[7..0] @ rs1_val[7..0],
    WZIP16P => rs2_val[31..16] @ rs1_val[31..16] @ rs2_val[15..0] @ rs1_val[15..0]
  };
  X(rdp @ 0b1) = result[63..32];
  X(rdp @ 0b0) = result[31..0];
  RETIRE_SUCCESS
}}

mapping p_widening_zip_mapping : p_widening_zip <-> string = {
  WZIP8P <-> "wzip8p",
  WZIP16P <-> "wzip16p",
}

mapping clause assembly = PEXT_WIDENING_ZIP(rs1, rs2, rdp, p_inst)
  <-> p_widening_zip_mapping(p_inst) ^ spc() ^ preg_name(rdp) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)

/* ****************************************************************** */

union clause ast = PEXT_WIDENING_ELEMENTARY_B : (regidx, regidx, pregidx, p_widening_elementary_b)

mapping clause encdec = PEXT_WIDENING_ELEMENTARY_B(rs1, rs2, rdp, PWADD_B) <->
  0b0 @ 0b0000 @ 0b10 @ rs2 @ rs1 @ 0b010 @ rdp @ 0b10011011
mapping clause encdec = PEXT_WIDENING_ELEMENTARY_B(rs1, rs2, rdp, PWADDA_B) <->
  0b0 @ 0b0001 @ 0b10 @ rs2 @ rs1 @ 0b010 @ rdp @ 0b10011011
mapping clause encdec = PEXT_WIDENING_ELEMENTARY_B(rs1, rs2, rdp, PWADDU_B) <->
  0b0 @ 0b0010 @ 0b10 @ rs2 @ rs1 @ 0b010 @ rdp @ 0b10011011
mapping clause encdec = PEXT_WIDENING_ELEMENTARY_B(rs1, rs2, rdp, PWADDAU_B) <->
  0b0 @ 0b0011 @ 0b10 @ rs2 @ rs1 @ 0b010 @ rdp @ 0b10011011
mapping clause encdec = PEXT_WIDENING_ELEMENTARY_B(rs1, rs2, rdp, PWMUL_B) <->
  0b0 @ 0b0100 @ 0b10 @ rs2 @ rs1 @ 0b010 @ rdp @ 0b10011011
mapping clause encdec = PEXT_WIDENING_ELEMENTARY_B(rs1, rs2, rdp, PWMULU_B) <->
  0b0 @ 0b0110 @ 0b10 @ rs2 @ rs1 @ 0b010 @ rdp @ 0b10011011
mapping clause encdec = PEXT_WIDENING_ELEMENTARY_B(rs1, rs2, rdp, PWSUB_B) <->
  0b0 @ 0b1000 @ 0b10 @ rs2 @ rs1 @ 0b010 @ rdp @ 0b10011011
mapping clause encdec = PEXT_WIDENING_ELEMENTARY_B(rs1, rs2, rdp, PWSUBA_B) <->
  0b0 @ 0b1001 @ 0b10 @ rs2 @ rs1 @ 0b010 @ rdp @ 0b10011011
mapping clause encdec = PEXT_WIDENING_ELEMENTARY_B(rs1, rs2, rdp, PWSUBU_B) <->
  0b0 @ 0b1010 @ 0b10 @ rs2 @ rs1 @ 0b010 @ rdp @ 0b10011011
mapping clause encdec = PEXT_WIDENING_ELEMENTARY_B(rs1, rs2, rdp, PWSUBAU_B) <->
  0b0 @ 0b1011 @ 0b10 @ rs2 @ rs1 @ 0b010 @ rdp @ 0b10011011
mapping clause encdec = PEXT_WIDENING_ELEMENTARY_B(rs1, rs2, rdp, PWMULSU_B) <->
  0b0 @ 0b1100 @ 0b10 @ rs2 @ rs1 @ 0b010 @ rdp @ 0b10011011

function clause execute (PEXT_WIDENING_ELEMENTARY_B(rs1, rs2, rdp, op)) = {
  if rdp == 0x0 then RETIRE_SUCCESS else {
  let rs1_val = X(rs1);
  let rs2_val = X(rs2);
  let rd_val = X(rdp @ 0b1) @ X(rdp @ 0b0);
  var result : bits(64) = zeros();
  foreach (i from 0 to (32 - 8) by 8) {
    let rs1_byte = slice(rs1_val, i, 8);
    let rs2_byte = slice(rs2_val, i, 8);
    let rd_halfword = slice(rd_val, 2 * i, 16);
    result[(2*i+15)..(2*i)] = match op {
      PWADD_B => EXTS(rs1_byte) + EXTS(rs2_byte),
      PWADDA_B => rd_halfword + EXTS(rs1_byte) + EXTS(rs2_byte),
      PWADDU_B => EXTZ(rs1_byte) + EXTZ(rs2_byte),
      PWADDAU_B => rd_halfword + EXTZ(rs1_byte) + EXTZ(rs2_byte),
      PWMUL_B => muls(rs1_byte, rs2_byte),
      PWMULU_B => mulu(rs1_byte, rs2_byte),
      PWSUB_B => EXTS(rs1_byte) - EXTS(rs2_byte),
      PWSUBA_B => rd_halfword + EXTS(rs1_byte) - EXTS(rs2_byte),
      PWSUBU_B => EXTZ(rs1_byte) - EXTZ(rs2_byte),
      PWSUBAU_B => rd_halfword + EXTZ(rs1_byte) - EXTZ(rs2_byte),
      PWMULSU_B => mulsu(rs1_byte, rs2_byte)
    };
  };
  X(rdp @ 0b1) = result[63..32];
  X(rdp @ 0b0) = result[31..0];
  RETIRE_SUCCESS
}}

mapping p_widening_elementary_b_mapping : p_widening_elementary_b <-> string = {
  PWADD_B <-> "pwadd.b",
  PWADDA_B <-> "pwadda.b",
  PWADDU_B <-> "pwaddu.b",
  PWADDAU_B <-> "pwaddau.b",
  PWMUL_B <-> "pwmul.b",
  PWMULU_B <-> "pwmulu.b",
  PWSUB_B <-> "pwsub.b",
  PWSUBA_B <-> "pwsuba.b",
  PWSUBU_B <-> "pwsubu.b",
  PWSUBAU_B <-> "pwsubau.b",
  PWMULSU_B <-> "pwmulsu.b"
}

mapping clause assembly = PEXT_WIDENING_ELEMENTARY_B(rs1, rs2, rdp, p_inst)
  <-> p_widening_elementary_b_mapping(p_inst) ^ spc() ^ preg_name(rdp) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)

/* ****************************************************************** */

union clause ast = PEXT_WIDENING_ELEMENTARY_H : (regidx, regidx, pregidx, p_widening_elementary_h)

mapping clause encdec = PEXT_WIDENING_ELEMENTARY_H(rs1, rs2, rdp, PWADD_H) <->
  0b0 @ 0b0000 @ 0b00 @ rs2 @ rs1 @ 0b010 @ rdp @ 0b10011011
mapping clause encdec = PEXT_WIDENING_ELEMENTARY_H(rs1, rs2, rdp, PWADDA_H) <->
  0b0 @ 0b0001 @ 0b00 @ rs2 @ rs1 @ 0b010 @ rdp @ 0b10011011
mapping clause encdec = PEXT_WIDENING_ELEMENTARY_H(rs1, rs2, rdp, PWADDU_H) <->
  0b0 @ 0b0010 @ 0b00 @ rs2 @ rs1 @ 0b010 @ rdp @ 0b10011011
mapping clause encdec = PEXT_WIDENING_ELEMENTARY_H(rs1, rs2, rdp, PWADDAU_H) <->
  0b0 @ 0b0011 @ 0b00 @ rs2 @ rs1 @ 0b010 @ rdp @ 0b10011011
mapping clause encdec = PEXT_WIDENING_ELEMENTARY_H(rs1, rs2, rdp, PWMUL_H) <->
  0b0 @ 0b0100 @ 0b00 @ rs2 @ rs1 @ 0b010 @ rdp @ 0b10011011
mapping clause encdec = PEXT_WIDENING_ELEMENTARY_H(rs1, rs2, rdp, PWMACC_H) <->
  0b0 @ 0b0101 @ 0b00 @ rs2 @ rs1 @ 0b010 @ rdp @ 0b10011011
mapping clause encdec = PEXT_WIDENING_ELEMENTARY_H(rs1, rs2, rdp, PWMULU_H) <->
  0b0 @ 0b0110 @ 0b00 @ rs2 @ rs1 @ 0b010 @ rdp @ 0b10011011
mapping clause encdec = PEXT_WIDENING_ELEMENTARY_H(rs1, rs2, rdp, PWMACCU_H) <->
  0b0 @ 0b0111 @ 0b00 @ rs2 @ rs1 @ 0b010 @ rdp @ 0b10011011
mapping clause encdec = PEXT_WIDENING_ELEMENTARY_H(rs1, rs2, rdp, PWSUB_H) <->
  0b0 @ 0b1000 @ 0b00 @ rs2 @ rs1 @ 0b010 @ rdp @ 0b10011011
mapping clause encdec = PEXT_WIDENING_ELEMENTARY_H(rs1, rs2, rdp, PWSUBA_H) <->
  0b0 @ 0b1001 @ 0b00 @ rs2 @ rs1 @ 0b010 @ rdp @ 0b10011011
mapping clause encdec = PEXT_WIDENING_ELEMENTARY_H(rs1, rs2, rdp, PWSUBU_H) <->
  0b0 @ 0b1010 @ 0b00 @ rs2 @ rs1 @ 0b010 @ rdp @ 0b10011011
mapping clause encdec = PEXT_WIDENING_ELEMENTARY_H(rs1, rs2, rdp, PWSUBAU_H) <->
  0b0 @ 0b1011 @ 0b00 @ rs2 @ rs1 @ 0b010 @ rdp @ 0b10011011
mapping clause encdec = PEXT_WIDENING_ELEMENTARY_H(rs1, rs2, rdp, PWMULSU_H) <->
  0b0 @ 0b1100 @ 0b00 @ rs2 @ rs1 @ 0b010 @ rdp @ 0b10011011
mapping clause encdec = PEXT_WIDENING_ELEMENTARY_H(rs1, rs2, rdp, PWMACCSU_H) <->
  0b0 @ 0b1101 @ 0b00 @ rs2 @ rs1 @ 0b010 @ rdp @ 0b10011011

function clause execute (PEXT_WIDENING_ELEMENTARY_H(rs1, rs2, rdp, op)) = {
  if rdp == 0x0 then RETIRE_SUCCESS else {
  let rs1_val = X(rs1);
  let rs2_val = X(rs2);
  let rd_val = X(rdp @ 0b1) @ X(rdp @ 0b0);
  var result : bits(64) = zeros();
  foreach (i from 0 to (32 - 16) by 16) {
    let rs1_halfword = slice(rs1_val, i, 16);
    let rs2_halfword = slice(rs2_val, i, 16);
    let rd_word = slice(rd_val, 2 * i, 32);
    result[(2*i+31)..(2*i)] = match op {
      PWADD_H => EXTS(rs1_halfword) + EXTS(rs2_halfword),
      PWADDA_H => rd_word + EXTS(rs1_halfword) + EXTS(rs2_halfword),
      PWADDU_H => EXTZ(rs1_halfword) + EXTZ(rs2_halfword),
      PWADDAU_H => rd_word + EXTZ(rs1_halfword) + EXTZ(rs2_halfword),
      PWMUL_H => muls(rs1_halfword, rs2_halfword),
      PWMACC_H => rd_word + muls(rs1_halfword, rs2_halfword),
      PWMULU_H => mulu(rs1_halfword, rs2_halfword),
      PWMACCU_H => rd_word + mulu(rs1_halfword, rs2_halfword),
      PWSUB_H => EXTS(rs1_halfword) - EXTS(rs2_halfword),
      PWSUBA_H => rd_word + EXTS(rs1_halfword) - EXTS(rs2_halfword),
      PWSUBU_H => EXTZ(rs1_halfword) - EXTZ(rs2_halfword),
      PWSUBAU_H => rd_word + EXTZ(rs1_halfword) - EXTZ(rs2_halfword),
      PWMULSU_H => mulsu(rs1_halfword, rs2_halfword),
      PWMACCSU_H => rd_word + mulsu(rs1_halfword, rs2_halfword)
    };
  };
  X(rdp @ 0b1) = result[63..32];
  X(rdp @ 0b0) = result[31..0];
  RETIRE_SUCCESS
}}

mapping p_widening_elementary_h_mapping : p_widening_elementary_h <-> string = {
  PWADD_H <-> "pwadd.h",
  PWADDA_H <-> "pwadda.h",
  PWADDU_H <-> "pwaddu.h",
  PWADDAU_H <-> "pwaddau.h",
  PWMUL_H <-> "pwmul.h",
  PWMACC_H <-> "pwmacc.h",
  PWMULU_H <-> "pwmulu.h",
  PWMACCU_H <-> "pwmaccu.h",
  PWSUB_H <-> "pwsub.h",
  PWSUBA_H <-> "pwsuba.h",
  PWSUBU_H <-> "pwsubu.h",
  PWSUBAU_H <-> "pwsubau.h",
  PWMULSU_H <-> "pwmulsu.h",
  PWMACCSU_H <-> "pwmaccsu.h"
}

mapping clause assembly = PEXT_WIDENING_ELEMENTARY_H(rs1, rs2, rdp, p_inst)
  <-> p_widening_elementary_h_mapping(p_inst) ^ spc() ^ preg_name(rdp) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)

/* ****************************************************************** */

union clause ast = PEXT_WIDENING_ELEMENTARY_W : (regidx, regidx, pregidx, p_widening_elementary_w)

mapping clause encdec = PEXT_WIDENING_ELEMENTARY_W(rs1, rs2, rdp, WADD) <->
  0b0 @ 0b0000 @ 0b01 @ rs2 @ rs1 @ 0b010 @ rdp @ 0b10011011
mapping clause encdec = PEXT_WIDENING_ELEMENTARY_W(rs1, rs2, rdp, WADDA) <->
  0b0 @ 0b0001 @ 0b01 @ rs2 @ rs1 @ 0b010 @ rdp @ 0b10011011
mapping clause encdec = PEXT_WIDENING_ELEMENTARY_W(rs1, rs2, rdp, WADDU) <->
  0b0 @ 0b0010 @ 0b01 @ rs2 @ rs1 @ 0b010 @ rdp @ 0b10011011
mapping clause encdec = PEXT_WIDENING_ELEMENTARY_W(rs1, rs2, rdp, WADDAU) <->
  0b0 @ 0b0011 @ 0b01 @ rs2 @ rs1 @ 0b010 @ rdp @ 0b10011011
mapping clause encdec = PEXT_WIDENING_ELEMENTARY_W(rs1, rs2, rdp, WMUL) <->
  0b0 @ 0b0100 @ 0b01 @ rs2 @ rs1 @ 0b010 @ rdp @ 0b10011011
mapping clause encdec = PEXT_WIDENING_ELEMENTARY_W(rs1, rs2, rdp, WMACC) <->
  0b0 @ 0b0101 @ 0b01 @ rs2 @ rs1 @ 0b010 @ rdp @ 0b10011011
mapping clause encdec = PEXT_WIDENING_ELEMENTARY_W(rs1, rs2, rdp, WMULU) <->
  0b0 @ 0b0110 @ 0b01 @ rs2 @ rs1 @ 0b010 @ rdp @ 0b10011011
mapping clause encdec = PEXT_WIDENING_ELEMENTARY_W(rs1, rs2, rdp, WMACCU) <->
  0b0 @ 0b0111 @ 0b01 @ rs2 @ rs1 @ 0b010 @ rdp @ 0b10011011
mapping clause encdec = PEXT_WIDENING_ELEMENTARY_W(rs1, rs2, rdp, WSUB) <->
  0b0 @ 0b1000 @ 0b01 @ rs2 @ rs1 @ 0b010 @ rdp @ 0b10011011
mapping clause encdec = PEXT_WIDENING_ELEMENTARY_W(rs1, rs2, rdp, WSUBA) <->
  0b0 @ 0b1001 @ 0b01 @ rs2 @ rs1 @ 0b010 @ rdp @ 0b10011011
mapping clause encdec = PEXT_WIDENING_ELEMENTARY_W(rs1, rs2, rdp, WSUBU) <->
  0b0 @ 0b1010 @ 0b01 @ rs2 @ rs1 @ 0b010 @ rdp @ 0b10011011
mapping clause encdec = PEXT_WIDENING_ELEMENTARY_W(rs1, rs2, rdp, WSUBAU) <->
  0b0 @ 0b1011 @ 0b01 @ rs2 @ rs1 @ 0b010 @ rdp @ 0b10011011
mapping clause encdec = PEXT_WIDENING_ELEMENTARY_W(rs1, rs2, rdp, WMULSU) <->
  0b0 @ 0b1100 @ 0b01 @ rs2 @ rs1 @ 0b010 @ rdp @ 0b10011011
mapping clause encdec = PEXT_WIDENING_ELEMENTARY_W(rs1, rs2, rdp, WMACCSU) <->
  0b0 @ 0b1101 @ 0b01 @ rs2 @ rs1 @ 0b010 @ rdp @ 0b10011011

function clause execute (PEXT_WIDENING_ELEMENTARY_W(rs1, rs2, rdp, op)) = {
  if rdp == 0x0 then RETIRE_SUCCESS else {
  let rs1_val = X(rs1);
  let rs2_val = X(rs2);
  let rd_val = X(rdp @ 0b1) @ X(rdp @ 0b0);
  var result : bits(64) = zeros();
  result = match op {
    WADD => EXTS(rs1_val) + EXTS(rs2_val),
    WADDA => rd_val + EXTS(rs1_val) + EXTS(rs2_val),
    WADDU => EXTZ(rs1_val) + EXTZ(rs2_val),
    WADDAU => rd_val + EXTZ(rs1_val) + EXTZ(rs2_val),
    WMUL => muls(rs1_val, rs2_val),
    WMACC => rd_val + muls(rs1_val, rs2_val),
    WMULU => mulu(rs1_val, rs2_val),
    WMACCU => rd_val + mulu(rs1_val, rs2_val),
    WSUB => EXTS(rs1_val) - EXTS(rs2_val),
    WSUBA => rd_val + EXTS(rs1_val) - EXTS(rs2_val),
    WSUBU => EXTZ(rs1_val) - EXTZ(rs2_val),
    WSUBAU => rd_val + EXTZ(rs1_val) - EXTZ(rs2_val),
    WMULSU => mulsu(rs1_val, rs2_val),
    WMACCSU => rd_val + mulsu(rs1_val, rs2_val)
  };
  X(rdp @ 0b1) = result[63..32];
  X(rdp @ 0b0) = result[31..0];
  RETIRE_SUCCESS
}}

mapping p_widening_elementary_w_mapping : p_widening_elementary_w <-> string = {
  WADD <-> "wadd",
  WADDA <-> "wadda",
  WADDU <-> "waddu",
  WADDAU <-> "waddau",
  WMUL <-> "wmul",
  WMACC <-> "wmacc",
  WMULU <-> "wmulu",
  WMACCU <-> "wmaccu",
  WSUB <-> "wsub",
  WSUBA <-> "wsuba",
  WSUBU <-> "wsubu",
  WSUBAU <-> "wsubau",
  WMULSU <-> "wmulsu",
  WMACCSU <-> "wmaccsu"
}

mapping clause assembly = PEXT_WIDENING_ELEMENTARY_W(rs1, rs2, rdp, p_inst)
  <-> p_widening_elementary_w_mapping(p_inst) ^ spc() ^ preg_name(rdp) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)

/* ****************************************************************** */

union clause ast = PEXT_WIDENING_MUL2HORIZON_H : (regidx, regidx, pregidx, p_widening_mul2horizon_h)

mapping clause encdec = PEXT_WIDENING_MUL2HORIZON_H(rs1, rs2, rdp, PM2WADD_H) <->
  0b0 @ 0b0000 @ 0b11 @ rs2 @ rs1 @ 0b010 @ rdp @ 0b10011011
mapping clause encdec = PEXT_WIDENING_MUL2HORIZON_H(rs1, rs2, rdp, PM2WADDA_H) <->
  0b0 @ 0b0001 @ 0b11 @ rs2 @ rs1 @ 0b010 @ rdp @ 0b10011011
mapping clause encdec = PEXT_WIDENING_MUL2HORIZON_H(rs1, rs2, rdp, PM2WADD_HX) <->
  0b0 @ 0b0010 @ 0b11 @ rs2 @ rs1 @ 0b010 @ rdp @ 0b10011011
mapping clause encdec = PEXT_WIDENING_MUL2HORIZON_H(rs1, rs2, rdp, PM2WADDA_HX) <->
  0b0 @ 0b0011 @ 0b11 @ rs2 @ rs1 @ 0b010 @ rdp @ 0b10011011
mapping clause encdec = PEXT_WIDENING_MUL2HORIZON_H(rs1, rs2, rdp, PM2WADDU_H) <->
  0b0 @ 0b0100 @ 0b11 @ rs2 @ rs1 @ 0b010 @ rdp @ 0b10011011
mapping clause encdec = PEXT_WIDENING_MUL2HORIZON_H(rs1, rs2, rdp, PM2WADDAU_H) <->
  0b0 @ 0b0101 @ 0b11 @ rs2 @ rs1 @ 0b010 @ rdp @ 0b10011011
mapping clause encdec = PEXT_WIDENING_MUL2HORIZON_H(rs1, rs2, rdp, PM2WADDSU_H) <->
  0b0 @ 0b1100 @ 0b11 @ rs2 @ rs1 @ 0b010 @ rdp @ 0b10011011
mapping clause encdec = PEXT_WIDENING_MUL2HORIZON_H(rs1, rs2, rdp, PM2WADDASU_H) <->
  0b0 @ 0b1101 @ 0b11 @ rs2 @ rs1 @ 0b010 @ rdp @ 0b10011011
mapping clause encdec = PEXT_WIDENING_MUL2HORIZON_H(rs1, rs2, rdp, PM2WSUB_H) <->
  0b0 @ 0b1000 @ 0b11 @ rs2 @ rs1 @ 0b010 @ rdp @ 0b10011011
mapping clause encdec = PEXT_WIDENING_MUL2HORIZON_H(rs1, rs2, rdp, PM2WSUBA_H) <->
  0b0 @ 0b1001 @ 0b11 @ rs2 @ rs1 @ 0b010 @ rdp @ 0b10011011
mapping clause encdec = PEXT_WIDENING_MUL2HORIZON_H(rs1, rs2, rdp, PM2WSUB_HX) <->
  0b0 @ 0b1010 @ 0b11 @ rs2 @ rs1 @ 0b010 @ rdp @ 0b10011011
mapping clause encdec = PEXT_WIDENING_MUL2HORIZON_H(rs1, rs2, rdp, PM2WSUBA_HX) <->
  0b0 @ 0b1011 @ 0b11 @ rs2 @ rs1 @ 0b010 @ rdp @ 0b10011011

function clause execute (PEXT_WIDENING_MUL2HORIZON_H(rs1, rs2, rdp, op)) = {
  if rdp == 0x0 then RETIRE_SUCCESS else {
  let rs1_val = X(rs1);
  let rs2_val = X(rs2);
  let rd_val = X(rdp @ 0b1) @ X(rdp @ 0b0);
  var result : bits(64) = zeros();
  let rs1_halfword_even = slice(rs1_val, 0, 16);
  let rs2_halfword_even = slice(rs2_val, 0, 16);
  let rs1_halfword_odd = slice(rs1_val, 16, 16);
  let rs2_halfword_odd = slice(rs2_val, 16, 16);
  result = match op {
    PM2WADD_H => EXTS(muls(rs1_halfword_odd, rs2_halfword_odd)) + EXTS(muls(rs1_halfword_even, rs2_halfword_even)),
    PM2WADDA_H => rd_val + EXTS(muls(rs1_halfword_odd, rs2_halfword_odd)) + EXTS(muls(rs1_halfword_even, rs2_halfword_even)),
    PM2WADD_HX => EXTS(muls(rs1_halfword_odd, rs2_halfword_even)) + EXTS(muls(rs1_halfword_even, rs2_halfword_odd)),
    PM2WADDA_HX => rd_val + EXTS(muls(rs1_halfword_odd, rs2_halfword_even)) + EXTS(muls(rs1_halfword_even, rs2_halfword_odd)),
    PM2WADDU_H => EXTZ(mulu(rs1_halfword_odd, rs2_halfword_odd)) + EXTZ(mulu(rs1_halfword_even, rs2_halfword_even)),
    PM2WADDAU_H => rd_val + EXTZ(mulu(rs1_halfword_odd, rs2_halfword_odd)) + EXTZ(mulu(rs1_halfword_even, rs2_halfword_even)),
    PM2WADDSU_H => EXTS(mulsu(rs1_halfword_odd, rs2_halfword_odd)) + EXTS(mulsu(rs1_halfword_even, rs2_halfword_even)),
    PM2WADDASU_H => rd_val + EXTS(mulsu(rs1_halfword_odd, rs2_halfword_odd)) + EXTS(mulsu(rs1_halfword_even, rs2_halfword_even)),
    PM2WSUB_H => EXTS(muls(rs1_halfword_odd, rs2_halfword_odd)) - EXTS(muls(rs1_halfword_even, rs2_halfword_even)),
    PM2WSUBA_H => rd_val + EXTS(muls(rs1_halfword_odd, rs2_halfword_odd)) - EXTS(muls(rs1_halfword_even, rs2_halfword_even)),
    PM2WSUB_HX => EXTS(muls(rs1_halfword_odd, rs2_halfword_even)) - EXTS(muls(rs1_halfword_even, rs2_halfword_odd)),
    PM2WSUBA_HX => rd_val + EXTS(muls(rs1_halfword_odd, rs2_halfword_even)) - EXTS(muls(rs1_halfword_even, rs2_halfword_odd))
  };
  X(rdp @ 0b1) = result[63..32];
  X(rdp @ 0b0) = result[31..0];
  RETIRE_SUCCESS
}}

mapping p_widening_mul2horizon_h_mapping : p_widening_mul2horizon_h <-> string = {
  PM2WADD_H <-> "pm2wadd.h",
  PM2WADDA_H <-> "pm2wadda.h",
  PM2WADD_HX <-> "pm2wadd.hx",
  PM2WADDA_HX <-> "pm2wadda.hx",
  PM2WADDU_H <-> "pm2waddu.h",
  PM2WADDAU_H <-> "pm2waddau.h",
  PM2WADDSU_H <-> "pm2waddsu.h",
  PM2WADDASU_H <-> "pm2waddasu.h",
  PM2WSUB_H <-> "pm2wsub.h",
  PM2WSUBA_H <-> "pm2wsuba.h",
  PM2WSUB_HX <-> "pm2wsub.hx",
  PM2WSUBA_HX <-> "pm2wsuba.hx"
}

mapping clause assembly = PEXT_WIDENING_MUL2HORIZON_H(rs1, rs2, rdp, p_inst)
  <-> p_widening_mul2horizon_h_mapping(p_inst) ^ spc() ^ preg_name(rdp) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)

/* ****************************************************************** */

union clause ast = PEXT_WIDENING_MUL_H : (regidx, regidx, pregidx, p_widening_mul_h)

mapping clause encdec = PEXT_WIDENING_MUL_H(rs1, rs2, rdp, PMQWACC_H) <->
  0b0 @ 0b1111 @ 0b00 @ rs2 @ rs1 @ 0b010 @ rdp @ 0b10011011
mapping clause encdec = PEXT_WIDENING_MUL_H(rs1, rs2, rdp, PMQRWACC_H) <->
  0b0 @ 0b1111 @ 0b10 @ rs2 @ rs1 @ 0b010 @ rdp @ 0b10011011

function clause execute (PEXT_WIDENING_MUL_H(rs1, rs2, rdp, op)) = {
  if rdp == 0x0 then RETIRE_SUCCESS else {
  let rs1_val = X(rs1);
  let rs2_val = X(rs2);
  let rd_val = X(rdp @ 0b1) @ X(rdp @ 0b0);
  var result : bits(64) = zeros();
  foreach (i from 0 to (32 - 16) by 16) {
    let rs1_halfword = slice(rs1_val, i, 16);
    let rs2_halfword = slice(rs2_val, i, 16);
    result[(2*i+31)..(2*i)] = match op {
      PMQWACC_H => rd_val[(2*i+31)..(2*i)] + EXTS(mulq(rs1_halfword, rs2_halfword)),
      PMQRWACC_H => rd_val[(2*i+31)..(2*i)] + EXTS(mulqr(rs1_halfword, rs2_halfword))
    };
  };
  X(rdp @ 0b1) = result[63..32];
  X(rdp @ 0b0) = result[31..0];
  RETIRE_SUCCESS
}}

mapping p_widening_mul_h_mapping : p_widening_mul_h <-> string = {
  PMQWACC_H <-> "pmqwacc.h",
  PMQRWACC_H <-> "pmqrwacc.h"
}

mapping clause assembly = PEXT_WIDENING_MUL_H(rs1, rs2, rdp, p_inst)
  <-> p_widening_mul_h_mapping(p_inst) ^ spc() ^ preg_name(rdp) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)

/* ****************************************************************** */

union clause ast = PEXT_WIDENING_MUL_W : (regidx, regidx, pregidx, p_widening_mul_w)

mapping clause encdec = PEXT_WIDENING_MUL_W(rs1, rs2, rdp, PMQWACC) <->
  0b0 @ 0b1111 @ 0b01 @ rs2 @ rs1 @ 0b010 @ rdp @ 0b10011011
mapping clause encdec = PEXT_WIDENING_MUL_W(rs1, rs2, rdp, PMQRWACC) <->
  0b0 @ 0b1111 @ 0b11 @ rs2 @ rs1 @ 0b010 @ rdp @ 0b10011011

function clause execute (PEXT_WIDENING_MUL_W(rs1, rs2, rdp, op)) = {
  if rdp == 0x0 then RETIRE_SUCCESS else {
  let rs1_val = X(rs1);
  let rs2_val = X(rs2);
  let rd_val = X(rdp @ 0b1) @ X(rdp @ 0b0);
  var result : bits(64) = zeros();
  result = match op {
    PMQWACC => rd_val + EXTS(mulq(rs1_val, rs2_val)),
    PMQRWACC => rd_val + EXTS(mulqr(rs1_val, rs2_val))
  };
  X(rdp @ 0b1) = result[63..32];
  X(rdp @ 0b0) = result[31..0];
  RETIRE_SUCCESS
}}

mapping p_widening_mul_w_mapping : p_widening_mul_w <-> string = {
  PMQWACC <-> "pmqwacc",
  PMQRWACC <-> "pmqrwacc"
}

mapping clause assembly = PEXT_WIDENING_MUL_W(rs1, rs2, rdp, p_inst)
  <-> p_widening_mul_w_mapping(p_inst) ^ spc() ^ preg_name(rdp) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)
