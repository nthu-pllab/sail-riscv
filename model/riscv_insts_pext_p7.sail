union clause ast = PEXT_PS : (regidx, regidx, p_ps)

mapping clause encdec = PEXT_PS(rs1, rd, PSABS_B) <->
  0b11100 @ 0b10 @ 0b00111 @ rs1 @ 0b010 @ rd @ 0b0011011
mapping clause encdec = PEXT_PS(rs1, rd, PSABS_H) <->
  0b11100 @ 0b00 @ 0b00111 @ rs1 @ 0b010 @ rd @ 0b0011011
mapping clause encdec = PEXT_PS(rs1, rd, PSEXT_H_B) <->
  0b11100 @ 0b00 @ 0b00100 @ rs1 @ 0b010 @ rd @ 0b0011011
mapping clause encdec = PEXT_PS(rs1, rd, PSEXT_W_B) if sizeof(xlen) == 64 <->
  0b11100 @ 0b01 @ 0b00100 @ rs1 @ 0b010 @ rd @ 0b0011011 if sizeof(xlen) == 64
mapping clause encdec = PEXT_PS(rs1, rd, PSEXT_W_H) if sizeof(xlen) == 64 <->
  0b11100 @ 0b01 @ 0b00101 @ rs1 @ 0b010 @ rd @ 0b0011011 if sizeof(xlen) == 64

function clause execute (PEXT_PS(rs1, rd, op)) = { // TODO: Double check if this is correct.
  let rs1_val = X(rs1);
  var result : xlenbits = zeros();
  match op {
    PSABS_B => {
      foreach (i from 0 to (sizeof(xlen) - 8) by 8) {
        let rs1_byte = slice(rs1_val, i, 8);
        result[(i+7)..i] = sabs(rs1_byte)
      };
    },
    PSABS_H => {
      foreach (i from 0 to (sizeof(xlen) - 16) by 16) {
        let rs1_halfword = slice(rs1_val, i, 16);
        result[(i+15)..i] = sabs(rs1_halfword)
      };
    },
    PSEXT_H_B => {
      foreach (i from 0 to (sizeof(xlen) - 16) by 16) {
        result[(i+15)..i] = EXTS(rs1_val[(i+7)..i])
      };  
    },
    PSEXT_W_B => {
      foreach (i from 0 to (sizeof(xlen) - 32) by 32) {
        result[(i+31)..i] = EXTS(rs1_val[(i+7)..i])
      };  
    },
    PSEXT_W_H => {
      foreach (i from 0 to (sizeof(xlen) - 32) by 32) {
        result[(i+31)..i] = EXTS(rs1_val[(i+15)..i])
      };  
    }
  };
  X(rd) = result;
  RETIRE_SUCCESS
}

mapping p_ps_mapping : p_ps <-> string = {
  PSABS_B <-> "psabs.b",
  PSABS_H <-> "psabs.h",
  PSEXT_H_B <-> "psext.h.b",
  PSEXT_W_B <-> "psext.w.b",
  PSEXT_W_H <-> "psext.w.h"
}

mapping clause assembly = PEXT_PS(rs1, rd, p_inst)
  <-> p_ps_mapping(p_inst) ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1)

/* ****************************************************************** */

union clause ast = PEXT_LOAD_UPPER_IMM_H : (bits(10), regidx, p_load_upper_imm_h)

mapping clause encdec = PEXT_LOAD_UPPER_IMM_H(imm10, rd, PLUI_H) <->
  0b11110 @ 0b00 @ imm10 @ 0b010 @ rd @ 0b0011011

function clause execute (PEXT_LOAD_UPPER_IMM_H(imm10, rd, op)) = {
  var result : xlenbits = zeros();
  foreach (i from 0 to (sizeof(xlen) - 16) by 16) {
    result[(i+15)..i] = match op {
      PLUI_H => imm10[8..0] @ imm10[9..9] @ sail_zeros(6)
    };
  };
  X(rd) = result;
  RETIRE_SUCCESS
}

mapping p_load_upper_imm_h_mapping : p_load_upper_imm_h <-> string = {
  PLUI_H <-> "plui.h"
}

mapping clause assembly = PEXT_LOAD_UPPER_IMM_H(imm10, rd, p_inst)
  <-> p_load_upper_imm_h_mapping(p_inst) ^ spc() ^ reg_name(rd) ^ sep() ^ hex_bits_10(imm10[0] @ imm10[9..1])

/* ****************************************************************** */

union clause ast = PEXT_LOAD_UPPER_IMM_W : (bits(10), regidx, p_load_upper_imm_w)

mapping clause encdec = PEXT_LOAD_UPPER_IMM_W(imm10, rd, PLUI_W) if sizeof(xlen) == 64 <->
  0b11110 @ 0b01 @ imm10 @ 0b010 @ rd @ 0b0011011 if sizeof(xlen) == 64

function clause execute (PEXT_LOAD_UPPER_IMM_W(imm10, rd, op)) = {
  var result : xlenbits = zeros();
  foreach (i from 0 to (sizeof(xlen) - 32) by 32) {
    result[(i+31)..i] = match op {
      PLUI_W => imm10[8..0] @ imm10[9..9] @ sail_zeros(22)
    };
  };
  X(rd) = result;
  RETIRE_SUCCESS
}

mapping p_load_upper_imm_w_mapping : p_load_upper_imm_w <-> string = {
  PLUI_W <-> "plui.w"
}

mapping clause assembly = PEXT_LOAD_UPPER_IMM_W(imm10, rd, p_inst)
  <-> p_load_upper_imm_w_mapping(p_inst) ^ spc() ^ reg_name(rd) ^ sep() ^ hex_bits_10(imm10[0] @ imm10[9..1])
