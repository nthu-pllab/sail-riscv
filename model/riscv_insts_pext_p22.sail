union clause ast = PEXT_SHIFT_SAT_B_RV32 : (bits(3), pregidx, pregidx, p_shift_sat_b_rv32)

mapping clause encdec = PEXT_SHIFT_SAT_B_RV32(imm3, rs1p, rdp, PSRLI_DB) <->
  0b0 @ 0b000 @ 0b0 @ 0b0001 @ imm3 @ rs1p @ 0b1110 @ rdp @ 0b00011011
mapping clause encdec = PEXT_SHIFT_SAT_B_RV32(imm3, rs1p, rdp, PSRAI_DB) <->
  0b0 @ 0b100 @ 0b0 @ 0b0001 @ imm3 @ rs1p @ 0b1110 @ rdp @ 0b00011011

function clause execute (PEXT_SHIFT_SAT_B_RV32(imm3, rs1p, rdp, op)) = {
  let rs1_val = X(rs1p @ 0b1) @ X(rs1p @ 0b0);
  let sa : bits(8) = EXTZ(imm3);
  var result : bits(64) = zeros();
  foreach (i from 0 to (64 - 8) by 8) {
    let rs1_byte = slice(rs1_val, i, 8);
    result[(i+7)..i] = match op {
      PSRLI_DB => shift_right_logic(rs1_byte, sa),
      PSRAI_DB => shift_right_arith(rs1_byte, sa)
    };
  };
  X(rdp @ 0b1) = result[63..32];
  X(rdp @ 0b0) = result[31..0];
  RETIRE_SUCCESS
}

mapping p_shift_sat_b_rv32_mapping : p_shift_sat_b_rv32 <-> string = {
  PSRLI_DB <-> "psrli.db",
  PSRAI_DB <-> "psrai.db"
}

mapping clause assembly = PEXT_SHIFT_SAT_B_RV32(imm3, rs1p, rdp, p_inst)
  <-> p_shift_sat_b_rv32_mapping(p_inst) ^ spc() ^ preg_name(rdp) ^ sep() ^ preg_name(rs1p) ^ sep() ^ hex_bits_3(imm3)

/* ****************************************************************** */

union clause ast = PEXT_SHIFT_SAT_H_RV32 : (bits(4), pregidx, pregidx, p_shift_sat_h_rv32)

mapping clause encdec = PEXT_SHIFT_SAT_H_RV32(imm4, rs1p, rdp, PSRLI_DH) <->
  0b0 @ 0b000 @ 0b0 @ 0b001 @ imm4 @ rs1p @ 0b1110 @ rdp @ 0b00011011
mapping clause encdec = PEXT_SHIFT_SAT_H_RV32(imm4, rs1p, rdp, PUSATI_DH) <->
  0b0 @ 0b010 @ 0b0 @ 0b001 @ imm4 @ rs1p @ 0b1110 @ rdp @ 0b00011011
mapping clause encdec = PEXT_SHIFT_SAT_H_RV32(imm4, rs1p, rdp, PSRAI_DH) <->
  0b0 @ 0b100 @ 0b0 @ 0b001 @ imm4 @ rs1p @ 0b1110 @ rdp @ 0b00011011
mapping clause encdec = PEXT_SHIFT_SAT_H_RV32(imm4, rs1p, rdp, PSRARI_DH) <->
  0b0 @ 0b101 @ 0b0 @ 0b001 @ imm4 @ rs1p @ 0b1110 @ rdp @ 0b00011011
mapping clause encdec = PEXT_SHIFT_SAT_H_RV32(imm4, rs1p, rdp, PSATI_DH) <->
  0b0 @ 0b110 @ 0b0 @ 0b001 @ imm4 @ rs1p @ 0b1110 @ rdp @ 0b00011011

function clause execute (PEXT_SHIFT_SAT_H_RV32(imm4, rs1p, rdp, op)) = {
  let rs1_val = X(rs1p @ 0b1) @ X(rs1p @ 0b0);
  let sa : bits(8) = EXTZ(imm4);
  var result : bits(64) = zeros();
  foreach (i from 0 to (64 - 16) by 16) {
    let rs1_halfword = slice(rs1_val, i, 16);
    result[(i+15)..i] = match op {
      PSRLI_DH => shift_right_logic(rs1_halfword, sa),
      PUSATI_DH =>
        let maxval : bits(16) = ~(0xFFFF << sa) in
        if (rs1_halfword <_s 0x0000) then 0x0000
        else if (rs1_halfword >_s maxval) then maxval else rs1_halfword,
      PSRAI_DH => shift_right_arith(rs1_halfword, sa),
      PSRARI_DH => shift_right_arith_rounding(rs1_halfword, sa),
      PSATI_DH =>
        let minval : bits(16) = 0xFFFF << sa in
        let maxval = ~(minval) in
        if (rs1_halfword <_s minval) then minval
        else if (rs1_halfword >_s maxval) then maxval else rs1_halfword,
    };
  };
  X(rdp @ 0b1) = result[63..32];
  X(rdp @ 0b0) = result[31..0];
  RETIRE_SUCCESS
}

mapping p_shift_sat_h_rv32_mapping : p_shift_sat_h_rv32 <-> string = {
  PSRLI_DH <-> "psrli.dh",
  PUSATI_DH <-> "pusati.dh",
  PSRAI_DH <-> "psrai.dh",
  PSRARI_DH <-> "psrari.dh",
  PSATI_DH <-> "psati.dh"
}

mapping clause assembly = PEXT_SHIFT_SAT_H_RV32(imm4, rs1p, rdp, p_inst)
  <-> p_shift_sat_h_rv32_mapping(p_inst) ^ spc() ^ preg_name(rdp) ^ sep() ^ preg_name(rs1p) ^ sep() ^ hex_bits_4(imm4)

/* ****************************************************************** */

union clause ast = PEXT_SHIFT_SAT_W_RV32 : (bits(5), pregidx, pregidx, p_shift_sat_w_rv32)

mapping clause encdec = PEXT_SHIFT_SAT_W_RV32(imm5, rs1p, rdp, PSRLI_DW) <->
  0b0 @ 0b000 @ 0b0 @ 0b01 @ imm5 @ rs1p @ 0b1110 @ rdp @ 0b00011011
mapping clause encdec = PEXT_SHIFT_SAT_W_RV32(imm5, rs1p, rdp, PUSATI_DW) <->
  0b0 @ 0b010 @ 0b0 @ 0b01 @ imm5 @ rs1p @ 0b1110 @ rdp @ 0b00011011
mapping clause encdec = PEXT_SHIFT_SAT_W_RV32(imm5, rs1p, rdp, PSRAI_DW) <->
  0b0 @ 0b100 @ 0b0 @ 0b01 @ imm5 @ rs1p @ 0b1110 @ rdp @ 0b00011011
mapping clause encdec = PEXT_SHIFT_SAT_W_RV32(imm5, rs1p, rdp, PSRARI_DW) <->
  0b0 @ 0b101 @ 0b0 @ 0b01 @ imm5 @ rs1p @ 0b1110 @ rdp @ 0b00011011
mapping clause encdec = PEXT_SHIFT_SAT_W_RV32(imm5, rs1p, rdp, PSATI_DW) <->
  0b0 @ 0b110 @ 0b0 @ 0b01 @ imm5 @ rs1p @ 0b1110 @ rdp @ 0b00011011

function clause execute (PEXT_SHIFT_SAT_W_RV32(imm5, rs1p, rdp, op)) = {
  let rs1_val = X(rs1p @ 0b1) @ X(rs1p @ 0b0);
  let sa : bits(8) = EXTZ(imm5);
  var result : bits(64) = zeros();
  foreach (i from 0 to (64 - 32) by 32) {
    let rs1_word = slice(rs1_val, i, 32);
    result[(i+31)..i] = match op {
      PSRLI_DW => shift_right_logic(rs1_word, sa),
      PUSATI_DW =>
        let maxval : bits(32) = ~(0xFFFFFFFF << sa) in
        if (rs1_word <_s 0x00000000) then 0x00000000
        else if (rs1_word >_s maxval) then maxval else rs1_word,
      PSRAI_DW => shift_right_arith(rs1_word, sa),
      PSRARI_DW => shift_right_arith_rounding(rs1_word, sa),
      PSATI_DW =>
        let minval : bits(32) = 0xFFFFFFFF << sa in
        let maxval = ~(minval) in
        if (rs1_word <_s minval) then minval
        else if (rs1_word >_s maxval) then maxval else rs1_word,
    };
  };
  X(rdp @ 0b1) = result[63..32];
  X(rdp @ 0b0) = result[31..0];
  RETIRE_SUCCESS
}

mapping p_shift_sat_w_rv32_mapping : p_shift_sat_w_rv32 <-> string = {
  PSRLI_DW <-> "psrli.dw",
  PUSATI_DW <-> "pusati.dw",
  PSRAI_DW <-> "psrai.dw",
  PSRARI_DW <-> "psrari.dw",
  PSATI_DW <-> "psati.dw"
}

mapping clause assembly = PEXT_SHIFT_SAT_W_RV32(imm5, rs1p, rdp, p_inst)
  <-> p_shift_sat_w_rv32_mapping(p_inst) ^ spc() ^ preg_name(rdp) ^ sep() ^ preg_name(rs1p) ^ sep() ^ hex_bits_5(imm5)

/* ****************************************************************** */

union clause ast = PEXT_SHIFT_RV32 : (pregidx, regidx, pregidx, p_shift_rv32)

mapping clause encdec = PEXT_SHIFT_RV32(rs1p, rs2, rdp, PSRL_DBS) <->
  0b0 @ 0b000 @ 0b1 @ 0b10 @ rs2 @ rs1p @ 0b1110 @ rdp @ 0b00011011
mapping clause encdec = PEXT_SHIFT_RV32(rs1p, rs2, rdp, PSRA_DBS) <->
  0b0 @ 0b100 @ 0b1 @ 0b10 @ rs2 @ rs1p @ 0b1110 @ rdp @ 0b00011011
mapping clause encdec = PEXT_SHIFT_RV32(rs1p, rs2, rdp, PSRL_DHS) <->
  0b0 @ 0b000 @ 0b1 @ 0b00 @ rs2 @ rs1p @ 0b1110 @ rdp @ 0b00011011
mapping clause encdec = PEXT_SHIFT_RV32(rs1p, rs2, rdp, PSRA_DHS) <->
  0b0 @ 0b100 @ 0b1 @ 0b00 @ rs2 @ rs1p @ 0b1110 @ rdp @ 0b00011011
mapping clause encdec = PEXT_SHIFT_RV32(rs1p, rs2, rdp, PSRL_DWS) <->
  0b0 @ 0b000 @ 0b1 @ 0b01 @ rs2 @ rs1p @ 0b1110 @ rdp @ 0b00011011
mapping clause encdec = PEXT_SHIFT_RV32(rs1p, rs2, rdp, PSRA_DWS) <->
  0b0 @ 0b100 @ 0b1 @ 0b01 @ rs2 @ rs1p @ 0b1110 @ rdp @ 0b00011011

function clause execute (PEXT_SHIFT_RV32(rs1p, rs2, rdp, op)) = {
  let rs1_val = X(rs1p @ 0b1) @ X(rs1p @ 0b0);
  let rs2_val = X(rs2);
  var result : bits(64) = zeros();
  match op {
    PSRL_DBS => {
      foreach (i from 0 to (64 - 8) by 8) {
        let rs1_byte = slice(rs1_val, i, 8);
        result[(i+7)..i] = shift_right_logic(rs1_byte, EXTZ(rs2_val[2..0]));
      };
    },
    PSRA_DBS => {
      foreach (i from 0 to (64 - 8) by 8) {
        let rs1_byte = slice(rs1_val, i, 8);
        result[(i+7)..i] = shift_right_arith(rs1_byte, EXTZ(rs2_val[2..0]));
      };
    },
    PSRL_DHS => {
      foreach (i from 0 to (64 - 16) by 16) {
        let rs1_halfword = slice(rs1_val, i, 16);
        result[(i+15)..i] = shift_right_logic(rs1_halfword, EXTZ(rs2_val[3..0]));
      };
    },
    PSRA_DHS => {
      foreach (i from 0 to (64 - 16) by 16) {
        let rs1_halfword = slice(rs1_val, i, 16);
        result[(i+15)..i] = shift_right_arith(rs1_halfword, EXTZ(rs2_val[3..0]));
      };
    },
    PSRL_DWS => {
      foreach (i from 0 to (64 - 32) by 32) {
        let rs1_word = slice(rs1_val, i, 32);
        result[(i+31)..i] = shift_right_logic(rs1_word, EXTZ(rs2_val[4..0]));
      };
    },
    PSRA_DWS => {
      foreach (i from 0 to (64 - 32) by 32) {
        let rs1_word = slice(rs1_val, i, 32);
        result[(i+31)..i] = shift_right_arith(rs1_word, EXTZ(rs2_val[4..0]));
      };
    }
  };
  X(rdp @ 0b1) = result[63..32];
  X(rdp @ 0b0) = result[31..0];
  RETIRE_SUCCESS
}

mapping p_shift_rv32_mapping : p_shift_rv32 <-> string = {
  PSRL_DBS <-> "psrl.dbs",
  PSRA_DBS <-> "psra.dbs",
  PSRL_DHS <-> "psrl.dhs",
  PSRA_DHS <-> "psra.dhs",
  PSRL_DWS <-> "psrl.dws",
  PSRA_DWS <-> "psra.dws"
}

mapping clause assembly = PEXT_SHIFT_RV32(rs1p, rs2, rdp, p_inst)
  <-> p_shift_rv32_mapping(p_inst) ^ spc() ^ preg_name(rdp) ^ sep() ^ preg_name(rs1p) ^ sep() ^ reg_name(rs2)
