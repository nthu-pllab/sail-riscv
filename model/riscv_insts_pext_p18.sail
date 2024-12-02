union clause ast = PEXT_WIDENING_SHIFT_LEFT_IMM_B : (bits(4), regidx, pregidx, p_widening_shift_left_imm_b)

mapping clause encdec = PEXT_WIDENING_SHIFT_LEFT_IMM_B(imm4, rs1, rdp, PWSLLI_B) <->
  0b0 @ 0b000 @ 0b0 @ 0b001 @ imm4 @ rs1 @ 0b010 @ rdp @ 0b00011011
mapping clause encdec = PEXT_WIDENING_SHIFT_LEFT_IMM_B(imm4, rs1, rdp, PWSLAI_B) <->
  0b0 @ 0b100 @ 0b0 @ 0b001 @ imm4 @ rs1 @ 0b010 @ rdp @ 0b00011011

function clause execute (PEXT_WIDENING_SHIFT_LEFT_IMM_B(imm4, rs1, rdp, op)) = {
  if rdp == 0x0 then RETIRE_SUCCESS else {
  let rs1_val = X(rs1);
  let sa : bits(8) = EXTZ(imm4);
  var result : bits(64) = zeros();
  foreach (i from 0 to (sizeof(xlen) - 8) by 8) {
    result[(2*i+15)..(2*i)] = match op {
      PWSLLI_B => shift_left_logic(0x00 @ rs1_val[(i+7)..i], sa),
      PWSLAI_B => if rs1_val[i+7] == 0b1[0] then shift_left_logic(0xff @ rs1_val[(i+7)..i], sa) else shift_left_logic(0x00 @ rs1_val[(i+7)..i], sa)
    };
  };
  X(rdp @ 0b1) = result[63..32];
  X(rdp @ 0b0) = result[31..0];
  RETIRE_SUCCESS
}}

mapping p_widening_shift_left_imm_b_mapping : p_widening_shift_left_imm_b <-> string = {
  PWSLLI_B <-> "pwslli.b",
  PWSLAI_B <-> "pwslai.b"
}

mapping clause assembly = PEXT_WIDENING_SHIFT_LEFT_IMM_B(imm4, rs1, rdp, p_inst)
  <-> p_widening_shift_left_imm_b_mapping(p_inst) ^ spc() ^ preg_name(rdp) ^ sep() ^ reg_name(rs1) ^ sep() ^ hex_bits_4(imm4)

/* ****************************************************************** */

union clause ast = PEXT_WIDENING_SHIFT_LEFT_IMM_H : (bits(5), regidx, pregidx, p_widening_shift_left_imm_h)

mapping clause encdec = PEXT_WIDENING_SHIFT_LEFT_IMM_H(imm5, rs1, rdp, PWSLLI_H) <->
  0b0 @ 0b000 @ 0b0 @ 0b01 @ imm5 @ rs1 @ 0b010 @ rdp @ 0b00011011
mapping clause encdec = PEXT_WIDENING_SHIFT_LEFT_IMM_H(imm5, rs1, rdp, PWSLAI_H) <->
  0b0 @ 0b100 @ 0b0 @ 0b01 @ imm5 @ rs1 @ 0b010 @ rdp @ 0b00011011

function clause execute (PEXT_WIDENING_SHIFT_LEFT_IMM_H(imm5, rs1, rdp, op)) = {
  if rdp == 0x0 then RETIRE_SUCCESS else {
  let rs1_val = X(rs1);
  let sa : bits(8) = EXTZ(imm5);
  var result : bits(64) = zeros();
  foreach (i from 0 to (sizeof(xlen) - 16) by 16) {
    result[(2*i+31)..(2*i)] = match op {
      PWSLLI_H => shift_left_logic(0x0000 @ rs1_val[(i+15)..i], sa),
      PWSLAI_H => if rs1_val[i+15] == 0b1[0] then shift_left_logic(0xffff @ rs1_val[(i+15)..i], sa) else shift_left_logic(0x0000 @ rs1_val[(i+15)..i], sa)
    };
  };
  X(rdp @ 0b1) = result[63..32];
  X(rdp @ 0b0) = result[31..0];
  RETIRE_SUCCESS
}}

mapping p_widening_shift_left_imm_h_mapping : p_widening_shift_left_imm_h <-> string = {
  PWSLLI_H <-> "pwslli.h",
  PWSLAI_H <-> "pwslai.h"
}

mapping clause assembly = PEXT_WIDENING_SHIFT_LEFT_IMM_H(imm5, rs1, rdp, p_inst)
  <-> p_widening_shift_left_imm_h_mapping(p_inst) ^ spc() ^ preg_name(rdp) ^ sep() ^ reg_name(rs1) ^ sep() ^ hex_bits_5(imm5)

/* ****************************************************************** */

union clause ast = PEXT_WIDENING_SHIFT_LEFT_IMM_W : (bits(6), regidx, pregidx, p_widening_shift_left_imm_w)

mapping clause encdec = PEXT_WIDENING_SHIFT_LEFT_IMM_W(imm6, rs1, rdp, WSLLI) <->
  0b0 @ 0b000 @ 0b0 @ 0b1 @ imm6 @ rs1 @ 0b010 @ rdp @ 0b00011011
mapping clause encdec = PEXT_WIDENING_SHIFT_LEFT_IMM_W(imm6, rs1, rdp, WSLAI) <->
  0b0 @ 0b100 @ 0b0 @ 0b1 @ imm6 @ rs1 @ 0b010 @ rdp @ 0b00011011

function clause execute (PEXT_WIDENING_SHIFT_LEFT_IMM_W(imm6, rs1, rdp, op)) = {
  if rdp == 0x0 then RETIRE_SUCCESS else {
  let rs1_val = X(rs1);
  let sa : bits(8) = EXTZ(imm6);
  var result : bits(64) = zeros();
  result = match op {
    WSLLI => shift_left_logic(0x00000000 @ rs1_val, sa),
    WSLAI => if rs1_val[31] == 0b1[0] then shift_left_logic(0xffffffff @ rs1_val[31..0], sa) else shift_left_logic(0x00000000 @ rs1_val[31..0], sa)
  };
  X(rdp @ 0b1) = result[63..32];
  X(rdp @ 0b0) = result[31..0];
  RETIRE_SUCCESS
}}

mapping p_widening_shift_left_imm_w_mapping : p_widening_shift_left_imm_w <-> string = {
  WSLLI <-> "wslli",
  WSLAI <-> "wslai"
}

mapping clause assembly = PEXT_WIDENING_SHIFT_LEFT_IMM_W(imm6, rs1, rdp, p_inst)
  <-> p_widening_shift_left_imm_w_mapping(p_inst) ^ spc() ^ preg_name(rdp) ^ sep() ^ reg_name(rs1) ^ sep() ^ hex_bits_6(imm6)

/* ****************************************************************** */

union clause ast = PEXT_LOAD_IMM_H_RV32 : (bits(10), pregidx, p_load_imm_h_rv32)

mapping clause encdec = PEXT_LOAD_IMM_H_RV32(imm10, rdp, PLI_DH) <->
  0b00110 @ 0b00 @ imm10 @ 0b010 @ rdp @ 0b00011011

function clause execute (PEXT_LOAD_IMM_H_RV32(imm10, rdp, op)) = {
  if rdp == 0x0 then RETIRE_SUCCESS else {
  var result : bits(64) = zeros();
  foreach (i from 0 to (64 - 16) by 16) {
    result[(i+15)..i] = match op {
      PLI_DH => if (imm10 & 0b0000000001) == 0b0000000001 then sail_ones(7) @ imm10[9..1] else sail_zeros(7) @ imm10[9..1]
    };
  };
  X(rdp @ 0b1) = result[63..32];
  X(rdp @ 0b0) = result[31..0];
  RETIRE_SUCCESS
}}

mapping p_load_imm_h_rv32_mapping : p_load_imm_h_rv32 <-> string = {
  PLI_DH <-> "pli.dh"
}

mapping clause assembly = PEXT_LOAD_IMM_H_RV32(imm10, rdp, p_inst)
  <-> p_load_imm_h_rv32_mapping(p_inst) ^ spc() ^ preg_name(rdp) ^ sep() ^ hex_bits_10(imm10[8..0] @ imm10[9])

/* ****************************************************************** */

union clause ast = PEXT_LOAD_IMM_B_RV32 : (bits(8), pregidx, p_load_imm_b_rv32)

mapping clause encdec = PEXT_LOAD_IMM_B_RV32(imm8, rdp, PLI_DB) <->
  0b00110 @ 0b100 @ imm8 @ 0b0010 @ rdp @ 0b00011011

function clause execute (PEXT_LOAD_IMM_B_RV32(imm8, rdp, op)) = {
  if rdp == 0x0 then RETIRE_SUCCESS else {
  var result : bits(64) = zeros();
  foreach (i from 0 to (64 - 8) by 8) {
    result[(i+7)..i] = match op {
      PLI_DB => imm8
    };
  };
  X(rdp @ 0b1) = result[63..32];
  X(rdp @ 0b0) = result[31..0];
  RETIRE_SUCCESS
}}

mapping p_load_imm_b_rv32_mapping : p_load_imm_b_rv32 <-> string = {
  PLI_DB <-> "pli.db"
}

mapping clause assembly = PEXT_LOAD_IMM_B_RV32(imm8, rdp, p_inst)
  <-> p_load_imm_b_rv32_mapping(p_inst) ^ spc() ^ preg_name(rdp) ^ sep() ^ hex_bits_8(imm8)

/* ****************************************************************** */

union clause ast = PEXT_LOAD_UPPER_IMM_H_RV32 : (bits(10), pregidx, p_load_upper_imm_h_rv32)

mapping clause encdec = PEXT_LOAD_UPPER_IMM_H_RV32(imm10, rdp, PLUI_DH) <->
  0b01110 @ 0b00 @ imm10 @ 0b010 @ rdp @ 0b00011011

function clause execute (PEXT_LOAD_UPPER_IMM_H_RV32(imm10, rdp, op)) = {
  if rdp == 0x0 then RETIRE_SUCCESS else {
  var result : bits(64) = zeros();
  foreach (i from 0 to (64 - 16) by 16) {
    result[(i+15)..i] = match op {
      PLUI_DH => imm10[8..0] @ slice (imm10, 9, 1) @ sail_zeros(6)
    };
  };
  X(rdp @ 0b1) = result[63..32];
  X(rdp @ 0b0) = result[31..0];
  RETIRE_SUCCESS
}}

mapping p_load_upper_imm_h_rv32_mapping : p_load_upper_imm_h_rv32 <-> string = {
  PLUI_DH <-> "plui.dh"
}

mapping clause assembly = PEXT_LOAD_UPPER_IMM_H_RV32(imm10, rdp, p_inst)
  <-> p_load_upper_imm_h_rv32_mapping(p_inst) ^ spc() ^ preg_name(rdp) ^ sep() ^ hex_bits_10(imm10[0] @ imm10[9..1])
