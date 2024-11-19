union clause ast = PEXT_SHIFT_SAT : (bits(6), regidx, regidx, p_shift_sat)

mapping clause encdec = PEXT_SHIFT_SAT(imm6, rs1, rd, USATI) <->
  0b1 @ 0b010 @ 0b0 @ 0b1 @ imm6 @ rs1 @ 0b100 @ rd @ 0b0011011
mapping clause encdec = PEXT_SHIFT_SAT(imm6, rs1, rd, SRARI) <->
  0b1 @ 0b101 @ 0b0 @ 0b1 @ imm6 @ rs1 @ 0b100 @ rd @ 0b0011011
mapping clause encdec = PEXT_SHIFT_SAT(imm6, rs1, rd, SATI) <->
  0b1 @ 0b110 @ 0b0 @ 0b1 @ imm6 @ rs1 @ 0b100 @ rd @ 0b0011011

function clause execute (PEXT_SHIFT_SAT(imm6, rs1, rd, op)) = {
  let rs1_val = X(rs1);
  let sa : bits(8) = EXTZ(imm6);
  var result : xlenbits = zeros();
  result = match op {
    USATI =>
      let maxval : bits(64) = ~(0xFFFFFFFFFFFFFFFF << sa) in
      if (rs1_val <_s 0x0000000000000000) then 0x0000000000000000
      else if (rs1_val >_s maxval) then maxval else rs1_val,
    SRARI => shift_right_arith_rounding(rs1_val, sa),
    SATI =>
      let minval : bits(64) = 0xFFFFFFFFFFFFFFFF << sa in
      let maxval = ~(minval) in
      if (rs1_val <_s minval) then minval
      else if (rs1_val >_s maxval) then maxval else rs1_val,
  };
  X(rd) = result;
  RETIRE_SUCCESS
}

mapping p_shift_sat_mapping : p_shift_sat <-> string = {
  USATI <-> "usati",
  SRARI <-> "srari",
  SATI <-> "sati"
}

mapping clause assembly = PEXT_SHIFT_SAT(imm6, rs1, rd, p_inst)
  <-> p_shift_sat_mapping(p_inst) ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ hex_bits_6(imm6)

/* ****************************************************************** */

union clause ast = PEXT_ZIP : (regidx, regidx, regidx, p_zip)

mapping clause encdec = PEXT_ZIP(rs1, rs2, rd, UNZIP8P) <->
  0b1 @ 0b110 @ 0b0 @ 0b00 @ rs2 @ rs1 @ 0b010 @ rd @ 0b0111011
mapping clause encdec = PEXT_ZIP(rs1, rs2, rd, UNZIP16P) <->
  0b1 @ 0b110 @ 0b0 @ 0b01 @ rs2 @ rs1 @ 0b010 @ rd @ 0b0111011
mapping clause encdec = PEXT_ZIP(rs1, rs2, rd, UNZIP8HP) <->
  0b1 @ 0b110 @ 0b0 @ 0b10 @ rs2 @ rs1 @ 0b010 @ rd @ 0b0111011
mapping clause encdec = PEXT_ZIP(rs1, rs2, rd, UNZIP16HP) <->
  0b1 @ 0b110 @ 0b0 @ 0b11 @ rs2 @ rs1 @ 0b010 @ rd @ 0b0111011
mapping clause encdec = PEXT_ZIP(rs1, rs2, rd, ZIP8P) <->
  0b1 @ 0b111 @ 0b0 @ 0b00 @ rs2 @ rs1 @ 0b010 @ rd @ 0b0111011
mapping clause encdec = PEXT_ZIP(rs1, rs2, rd, ZIP16P) <->
  0b1 @ 0b111 @ 0b0 @ 0b01 @ rs2 @ rs1 @ 0b010 @ rd @ 0b0111011
mapping clause encdec = PEXT_ZIP(rs1, rs2, rd, ZIP8HP) <->
  0b1 @ 0b111 @ 0b0 @ 0b10 @ rs2 @ rs1 @ 0b010 @ rd @ 0b0111011
mapping clause encdec = PEXT_ZIP(rs1, rs2, rd, ZIP16HP) <->
  0b1 @ 0b111 @ 0b0 @ 0b11 @ rs2 @ rs1 @ 0b010 @ rd @ 0b0111011

function clause execute (PEXT_ZIP(rs1, rs2, rd, op)) = {
  let rs1_val = X(rs1);
  let rs2_val = X(rs2);
  var result : xlenbits = zeros();
  result = match op {
    UNZIP8P => rs2_val[55..48] @ rs2_val[39..32] @ rs2_val[23..16] @ rs2_val[7..0]
                   @ rs1_val[55..48] @ rs1_val[39..32] @ rs1_val[23..16] @ rs1_val[7..0],
    UNZIP16P => rs2_val[47..32] @ rs2_val[15..0] @ rs1_val[47..32] @ rs1_val[15..0],
    UNZIP8HP => rs2_val[63..56] @ rs2_val[47..40] @ rs2_val[31..24] @ rs2_val[15..8]
                    @ rs1_val[63..56] @ rs1_val[47..40] @ rs1_val[31..24] @ rs1_val[15..8],
    UNZIP16HP => rs2_val[63..48] @ rs2_val[31..16] @ rs1_val[63..48] @ rs1_val[31..16],
    ZIP8P => rs2_val[31..24] @ rs1_val[31..24] @ rs2_val[23..16] @ rs1_val[23..16]
                 @ rs2_val[15..8] @ rs1_val[15..8] @ rs2_val[7..0] @ rs1_val[7..0],
    ZIP16P => rs2_val[31..16] @ rs1_val[31..16] @ rs2_val[15..0] @ rs1_val[15..0],
    ZIP8HP => rs2_val[63..56] @ rs1_val[63..56] @ rs2_val[55..48] @ rs1_val[55..48]
                  @ rs2_val[47..40] @ rs1_val[47..40] @ rs2_val[39..32] @ rs1_val[39..32],
    ZIP16HP => rs2_val[63..48] @ rs1_val[63..48] @ rs2_val[47..32] @ rs1_val[47..32],
  };
  X(rd) = result;
  RETIRE_SUCCESS
}

mapping p_zip_mapping : p_zip <-> string = {
  UNZIP8P <-> "unzip8p",
  UNZIP16P <-> "unzip16p",
  UNZIP8HP <-> "unzip8hp",
  UNZIP16HP <-> "unzip16hp",
  ZIP8P <-> "zip8p",
  ZIP16P <-> "zip16p",
  ZIP8HP <-> "zip8hp",
  ZIP16HP <-> "zip16hp"
}

mapping clause assembly = PEXT_ZIP(rs1, rs2, rd, p_inst)
  <-> p_zip_mapping(p_inst) ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)

/* ****************************************************************** */

union clause ast = PEXT_MUL_W : (regidx, regidx, regidx, p_mul_w)

mapping clause encdec = PEXT_MUL_W(rs1, rs2, rd, MUL_W00) <->
  0b1 @ 0b0000 @ 0b11 @ rs2 @ rs1 @ 0b011 @ rd @ 0b0111011
mapping clause encdec = PEXT_MUL_W(rs1, rs2, rd, MUL_W11) <->
  0b1 @ 0b0010 @ 0b11 @ rs2 @ rs1 @ 0b011 @ rd @ 0b0111011
mapping clause encdec = PEXT_MUL_W(rs1, rs2, rd, MULU_W00) <->
  0b1 @ 0b0100 @ 0b11 @ rs2 @ rs1 @ 0b011 @ rd @ 0b0111011
mapping clause encdec = PEXT_MUL_W(rs1, rs2, rd, MULU_W11) <->
  0b1 @ 0b0110 @ 0b11 @ rs2 @ rs1 @ 0b011 @ rd @ 0b0111011
mapping clause encdec = PEXT_MUL_W(rs1, rs2, rd, MULSU_W00) <->
  0b1 @ 0b1100 @ 0b11 @ rs2 @ rs1 @ 0b011 @ rd @ 0b0111011
mapping clause encdec = PEXT_MUL_W(rs1, rs2, rd, MULSU_W11) <->
  0b1 @ 0b1110 @ 0b11 @ rs2 @ rs1 @ 0b011 @ rd @ 0b0111011
mapping clause encdec = PEXT_MUL_W(rs1, rs2, rd, MACC_W00) <->
  0b1 @ 0b0001 @ 0b11 @ rs2 @ rs1 @ 0b011 @ rd @ 0b0111011
mapping clause encdec = PEXT_MUL_W(rs1, rs2, rd, MACC_W11) <->
  0b1 @ 0b0011 @ 0b11 @ rs2 @ rs1 @ 0b011 @ rd @ 0b0111011
mapping clause encdec = PEXT_MUL_W(rs1, rs2, rd, MACCU_W00) <->
  0b1 @ 0b0101 @ 0b11 @ rs2 @ rs1 @ 0b011 @ rd @ 0b0111011
mapping clause encdec = PEXT_MUL_W(rs1, rs2, rd, MACCU_W11) <->
  0b1 @ 0b0111 @ 0b11 @ rs2 @ rs1 @ 0b011 @ rd @ 0b0111011
mapping clause encdec = PEXT_MUL_W(rs1, rs2, rd, MACCSU_W00) <->
  0b1 @ 0b1101 @ 0b11 @ rs2 @ rs1 @ 0b011 @ rd @ 0b0111011
mapping clause encdec = PEXT_MUL_W(rs1, rs2, rd, MACCSU_W11) <->
  0b1 @ 0b1111 @ 0b11 @ rs2 @ rs1 @ 0b011 @ rd @ 0b0111011
mapping clause encdec = PEXT_MUL_W(rs1, rs2, rd, MQACC_W01) <->
  0b1 @ 0b1111 @ 0b01 @ rs2 @ rs1 @ 0b101 @ rd @ 0b0111011
mapping clause encdec = PEXT_MUL_W(rs1, rs2, rd, MQRACC_W01) <->
  0b1 @ 0b1111 @ 0b11 @ rs2 @ rs1 @ 0b101 @ rd @ 0b0111011

function clause execute (PEXT_MUL_W(rs1, rs2, rd, op)) = {
  let rs1_val = X(rs1);
  let rs2_val = X(rs2);
  let rd_val = X(rd);
  var result : xlenbits = zeros();
  let rs1_word_even = slice(rs1_val, 0, 32);
  let rs2_word_even = slice(rs2_val, 0, 32);
  let rs1_word_odd = slice(rs1_val, 32, 32);
  let rs2_word_odd = slice(rs2_val, 32, 32);
  result = match op {
    MUL_W00 => muls(rs1_word_even, rs2_word_even),
    MUL_W11 => muls(rs1_word_odd, rs2_word_odd),
    MULU_W00 => mulu(rs1_word_even, rs2_word_even),
    MULU_W11 => mulu(rs1_word_odd, rs2_word_odd),
    MULSU_W00 => mulsu(rs1_word_even, rs2_word_even),
    MULSU_W11 => mulsu(rs1_word_odd, rs2_word_odd),
    MACC_W00 => rd_val + muls(rs1_word_even, rs2_word_even),
    MACC_W11 => rd_val + muls(rs1_word_odd, rs2_word_odd),
    MACCU_W00 => rd_val + mulu(rs1_word_even, rs2_word_even),
    MACCU_W11 => rd_val + mulu(rs1_word_odd, rs2_word_odd),
    MACCSU_W00 => rd_val + mulsu(rs1_word_even, rs2_word_even),
    MACCSU_W11 => rd_val + mulsu(rs1_word_odd, rs2_word_odd),
    MQACC_W01 => rd_val + mulq(rs1_word_even, rs2_word_odd),
    MQRACC_W01 => rd_val + mulqr(rs1_word_even, rs2_word_odd)
  };
  X(rd) = result;
  RETIRE_SUCCESS
}

mapping p_mul_w_mapping : p_mul_w <-> string = {
  MUL_W00 <-> "mul.w00",
  MUL_W11 <-> "mul.w11",
  MULU_W00 <-> "mulu.w00",
  MULU_W11 <-> "mulu.w11",
  MULSU_W00 <-> "mulsu.w00",
  MULSU_W11 <-> "mulsu.w11",
  MACC_W00 <-> "macc.w00",
  MACC_W11 <-> "macc.w11",
  MACCU_W00 <-> "maccu.w00",
  MACCU_W11 <-> "maccu.w11",
  MACCSU_W00 <-> "maccsu.w00",
  MACCSU_W11 <-> "maccsu.w11",
  MQACC_W01 <-> "mqacc.w01",
  MQRACC_W01 <-> "mqracc.w01"
}

mapping clause assembly = PEXT_MUL_W(rs1, rs2, rd, p_inst)
  <-> p_mul_w_mapping(p_inst) ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)

/* ****************************************************************** */

union clause ast = PEXT_PACK : (regidx, regidx, regidx, p_pack)

mapping clause encdec = PEXT_PACK(rs1, rs2, rd, PACKBT) <->
  0b1 @ 0b001 @ 0b0 @ 0b11 @ rs2 @ rs1 @ 0b100 @ rd @ 0b0111011
mapping clause encdec = PEXT_PACK(rs1, rs2, rd, PACKTB) <->
  0b1 @ 0b010 @ 0b0 @ 0b11 @ rs2 @ rs1 @ 0b100 @ rd @ 0b0111011
mapping clause encdec = PEXT_PACK(rs1, rs2, rd, PACKT) <->
  0b1 @ 0b011 @ 0b0 @ 0b11 @ rs2 @ rs1 @ 0b100 @ rd @ 0b0111011

function clause execute (PEXT_PACK(rs1, rs2, rd, op)) = {
  let rs1_val = X(rs1);
  let rs2_val = X(rs2);
  var result : xlenbits = zeros();
  result = match op {
    PACKBT => rs2_val[63..32] @ rs1_val[31..0],
    PACKTB => rs2_val[31..0] @ rs1_val[63..32],
    PACKT => rs2_val[63..32] @ rs1_val[63..32]
  };
  X(rd) = result;
  RETIRE_SUCCESS
}

mapping p_pack_mapping : p_pack <-> string = {
  PACKBT <-> "packbt",
  PACKTB <-> "packtb",
  PACKT <-> "packt"
}

mapping clause assembly = PEXT_PACK(rs1, rs2, rd, p_inst)
  <-> p_pack_mapping(p_inst) ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)

/* ****************************************************************** */

union clause ast = PEXT_MUL2HORIZON_W : (regidx, regidx, regidx, p_mul2horizon_w)

mapping clause encdec = PEXT_MUL2HORIZON_W(rs1, rs2, rd, PM2ADD_W) <->
  0b1 @ 0b0000 @ 0b01 @ rs2 @ rs1 @ 0b101 @ rd @ 0b0111011
mapping clause encdec = PEXT_MUL2HORIZON_W(rs1, rs2, rd, PM2ADDA_W) <->
  0b1 @ 0b0001 @ 0b01 @ rs2 @ rs1 @ 0b101 @ rd @ 0b0111011
mapping clause encdec = PEXT_MUL2HORIZON_W(rs1, rs2, rd, PM2ADD_WX) <->
  0b1 @ 0b0010 @ 0b01 @ rs2 @ rs1 @ 0b101 @ rd @ 0b0111011
mapping clause encdec = PEXT_MUL2HORIZON_W(rs1, rs2, rd, PM2ADDA_WX) <->
  0b1 @ 0b0011 @ 0b01 @ rs2 @ rs1 @ 0b101 @ rd @ 0b0111011
mapping clause encdec = PEXT_MUL2HORIZON_W(rs1, rs2, rd, PM2ADDU_W) <->
  0b1 @ 0b0100 @ 0b01 @ rs2 @ rs1 @ 0b101 @ rd @ 0b0111011
mapping clause encdec = PEXT_MUL2HORIZON_W(rs1, rs2, rd, PM2ADDAU_W) <->
  0b1 @ 0b0101 @ 0b01 @ rs2 @ rs1 @ 0b101 @ rd @ 0b0111011
mapping clause encdec = PEXT_MUL2HORIZON_W(rs1, rs2, rd, PM2ADDSU_W) <->
  0b1 @ 0b1100 @ 0b01 @ rs2 @ rs1 @ 0b101 @ rd @ 0b0111011
mapping clause encdec = PEXT_MUL2HORIZON_W(rs1, rs2, rd, PM2ADDASU_W) <->
  0b1 @ 0b1101 @ 0b01 @ rs2 @ rs1 @ 0b101 @ rd @ 0b0111011
mapping clause encdec = PEXT_MUL2HORIZON_W(rs1, rs2, rd, PMQ2ADD_W) <->
  0b1 @ 0b0110 @ 0b01 @ rs2 @ rs1 @ 0b101 @ rd @ 0b0111011
mapping clause encdec = PEXT_MUL2HORIZON_W(rs1, rs2, rd, PMQ2ADDA_W) <->
  0b1 @ 0b0111 @ 0b01 @ rs2 @ rs1 @ 0b101 @ rd @ 0b0111011
mapping clause encdec = PEXT_MUL2HORIZON_W(rs1, rs2, rd, PMQR2ADD_W) <->
  0b1 @ 0b0110 @ 0b11 @ rs2 @ rs1 @ 0b101 @ rd @ 0b0111011
mapping clause encdec = PEXT_MUL2HORIZON_W(rs1, rs2, rd, PMQR2ADDA_W) <->
  0b1 @ 0b0111 @ 0b11 @ rs2 @ rs1 @ 0b101 @ rd @ 0b0111011
mapping clause encdec = PEXT_MUL2HORIZON_W(rs1, rs2, rd, PM2SUB_W) <->
  0b1 @ 0b1000 @ 0b01 @ rs2 @ rs1 @ 0b101 @ rd @ 0b0111011
mapping clause encdec = PEXT_MUL2HORIZON_W(rs1, rs2, rd, PM2SUBA_W) <->
  0b1 @ 0b1001 @ 0b01 @ rs2 @ rs1 @ 0b101 @ rd @ 0b0111011
mapping clause encdec = PEXT_MUL2HORIZON_W(rs1, rs2, rd, PM2SUB_WX) <->
  0b1 @ 0b1010 @ 0b01 @ rs2 @ rs1 @ 0b101 @ rd @ 0b0111011
mapping clause encdec = PEXT_MUL2HORIZON_W(rs1, rs2, rd, PM2SUBA_WX) <->
  0b1 @ 0b1011 @ 0b01 @ rs2 @ rs1 @ 0b101 @ rd @ 0b0111011

function clause execute (PEXT_MUL2HORIZON_W(rs1, rs2, rd, op)) = {
  let rs1_val = X(rs1);
  let rs2_val = X(rs2);
  let rd_val = X(rd);
  var result : xlenbits = zeros();
  let rs1_byte_even = slice(rs1_val, 0, 32);
  let rs2_byte_even = slice(rs2_val, 0, 32);
  let rs1_byte_odd = slice(rs1_val, 32, 32);
  let rs2_byte_odd = slice(rs2_val, 32, 32);
  result = match op {
    PM2ADD_W => muls(rs1_byte_odd, rs2_byte_odd) + muls(rs1_byte_even, rs2_byte_even),
    PM2ADDA_W => rd_val + muls(rs1_byte_odd, rs2_byte_odd) + muls(rs1_byte_even, rs2_byte_even),
    PM2ADD_WX => muls(rs1_byte_odd, rs2_byte_even) + muls(rs1_byte_even, rs2_byte_odd),
    PM2ADDA_WX => rd_val + muls(rs1_byte_odd, rs2_byte_even) + muls(rs1_byte_even, rs2_byte_odd),
    PM2ADDU_W => mulu(rs1_byte_odd, rs2_byte_odd) + mulu(rs1_byte_even, rs2_byte_even),
    PM2ADDAU_W => rd_val + mulu(rs1_byte_odd, rs2_byte_odd) + mulu(rs1_byte_even, rs2_byte_even),
    PM2ADDSU_W => mulsu(rs1_byte_odd, rs2_byte_odd) + mulsu(rs1_byte_even, rs2_byte_even),
    PM2ADDASU_W => rd_val + mulsu(rs1_byte_odd, rs2_byte_odd) + mulsu(rs1_byte_even, rs2_byte_even),
    PMQ2ADD_W => mulq(rs1_byte_odd, rs2_byte_odd) + mulq(rs1_byte_even, rs2_byte_even),
    PMQ2ADDA_W => rd_val + mulq(rs1_byte_odd, rs2_byte_odd) + mulq(rs1_byte_even, rs2_byte_even),
    PMQR2ADD_W => mulqr(rs1_byte_odd, rs2_byte_odd) + mulqr(rs1_byte_even, rs2_byte_even),
    PMQR2ADDA_W => rd_val + mulqr(rs1_byte_odd, rs2_byte_odd) + mulqr(rs1_byte_even, rs2_byte_even),
    PM2SUB_W => muls(rs1_byte_odd, rs2_byte_odd) - muls(rs1_byte_even, rs2_byte_even),
    PM2SUBA_W => rd_val + muls(rs1_byte_odd, rs2_byte_odd) - muls(rs1_byte_even, rs2_byte_even),
    PM2SUB_WX => muls(rs1_byte_odd, rs2_byte_even) - muls(rs1_byte_even, rs2_byte_odd),
    PM2SUBA_WX => rd_val + muls(rs1_byte_odd, rs2_byte_even) - muls(rs1_byte_even, rs2_byte_odd)
  };
  X(rd) = result;
  RETIRE_SUCCESS
}

mapping p_mul2horizon_w_mapping : p_mul2horizon_w <-> string = {
  PM2ADD_W <-> "pm2add.w",
  PM2ADDA_W <-> "pm2adda.w",
  PM2ADD_WX <-> "pm2add.wx",
  PM2ADDA_WX <-> "pm2adda.wx",
  PM2ADDU_W <-> "pm2addu.w",
  PM2ADDAU_W <-> "pm2addau.w",
  PM2ADDSU_W <-> "pm2addsu.w",
  PM2ADDASU_W <-> "pm2addasu.w",
  PMQ2ADD_W <-> "pmq2add.w",
  PMQ2ADDA_W <-> "pmq2adda.w",
  PMQR2ADD_W <-> "pmqr2add.w",
  PMQR2ADDA_W <-> "pmqr2adda.w",
  PM2SUB_W <-> "pm2sub.w",
  PM2SUBA_W <-> "pm2suba.w",
  PM2SUB_WX <-> "pm2sub.wx",
  PM2SUBA_WX <-> "pm2suba.wx"
}

mapping clause assembly = PEXT_MUL2HORIZON_W(rs1, rs2, rd, p_inst)
  <-> p_mul2horizon_w_mapping(p_inst) ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)

/* ****************************************************************** */

union clause ast = PEXT_MUL4HORIZON_H : (regidx, regidx, regidx, p_mul4horizon_h)

mapping clause encdec = PEXT_MUL4HORIZON_H(rs1, rs2, rd, PM4ADD_H) <->
  0b1 @ 0b0000 @ 0b11 @ rs2 @ rs1 @ 0b101 @ rd @ 0b0111011
mapping clause encdec = PEXT_MUL4HORIZON_H(rs1, rs2, rd, PM4ADDA_H) <->
  0b1 @ 0b0001 @ 0b11 @ rs2 @ rs1 @ 0b101 @ rd @ 0b0111011
mapping clause encdec = PEXT_MUL4HORIZON_H(rs1, rs2, rd, PM4ADDU_H) <->
  0b1 @ 0b0100 @ 0b11 @ rs2 @ rs1 @ 0b101 @ rd @ 0b0111011
mapping clause encdec = PEXT_MUL4HORIZON_H(rs1, rs2, rd, PM4ADDAU_H) <->
  0b1 @ 0b0101 @ 0b11 @ rs2 @ rs1 @ 0b101 @ rd @ 0b0111011
mapping clause encdec = PEXT_MUL4HORIZON_H(rs1, rs2, rd, PM4ADDSU_H) <->
  0b1 @ 0b1100 @ 0b11 @ rs2 @ rs1 @ 0b101 @ rd @ 0b0111011
mapping clause encdec = PEXT_MUL4HORIZON_H(rs1, rs2, rd, PM4ADDASU_H) <->
  0b1 @ 0b1101 @ 0b11 @ rs2 @ rs1 @ 0b101 @ rd @ 0b0111011

function clause execute (PEXT_MUL4HORIZON_H(rs1, rs2, rd, op)) = {
  let rs1_val = X(rs1);
  let rs2_val = X(rs2);
  let rd_val = X(rd);
  var result : xlenbits = match op {
    PM4ADD_H => zeros(),
    PM4ADDA_H => rd_val,
    PM4ADDU_H => zeros(),
    PM4ADDAU_H => rd_val,
    PM4ADDSU_H => zeros(),
    PM4ADDASU_H => rd_val
  };
  foreach (i from 0 to (sizeof(xlen) - 16) by 16) {
    let rs1_halfword = slice(rs1_val, i, 16);
    let rs2_halfword = slice(rs2_val, i, 16);
    result = match op {
      PM4ADD_H => result + EXTS(muls(rs1_halfword, rs2_halfword)),
      PM4ADDA_H => result + EXTS(muls(rs1_halfword, rs2_halfword)),
      PM4ADDU_H => result + EXTZ(mulu(rs1_halfword, rs2_halfword)),
      PM4ADDAU_H => result + EXTZ(mulu(rs1_halfword, rs2_halfword)),
      PM4ADDSU_H => result + EXTS(mulsu(rs1_halfword, rs2_halfword)),
      PM4ADDASU_H => result + EXTS(mulsu(rs1_halfword, rs2_halfword))
    };
  };
  X(rd) = result;
  RETIRE_SUCCESS
}

mapping p_mul4horizon_h_mapping : p_mul4horizon_h <-> string = {
  PM4ADD_H <-> "pm4add.h",
  PM4ADDA_H <-> "pm4adda.h",
  PM4ADDU_H <-> "pm4addu.h",
  PM4ADDAU_H <-> "pm4addau.h",
  PM4ADDSU_H <-> "pm4addsu.h",
  PM4ADDASU_H <-> "pm4addasu.h"
}

mapping clause assembly = PEXT_MUL4HORIZON_H(rs1, rs2, rd, p_inst)
  <-> p_mul4horizon_h_mapping(p_inst) ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)

/* ****************************************************************** */

union clause ast = PEXT_ADDSUB_W : (regidx, regidx, regidx, p_addsub_w)

mapping clause encdec = PEXT_ADDSUB_W(rs1, rs2, rd, PAS_WX) <->
  0b1 @ 0b0000 @ 0b01 @ rs2 @ rs1 @ 0b110 @ rd @ 0b0111011
mapping clause encdec = PEXT_ADDSUB_W(rs1, rs2, rd, PSA_WX) <->
  0b1 @ 0b0000 @ 0b11 @ rs2 @ rs1 @ 0b110 @ rd @ 0b0111011
mapping clause encdec = PEXT_ADDSUB_W(rs1, rs2, rd, PSAS_WX) <->
  0b1 @ 0b0010 @ 0b01 @ rs2 @ rs1 @ 0b110 @ rd @ 0b0111011
mapping clause encdec = PEXT_ADDSUB_W(rs1, rs2, rd, PSSA_WX) <->
  0b1 @ 0b0010 @ 0b11 @ rs2 @ rs1 @ 0b110 @ rd @ 0b0111011
mapping clause encdec = PEXT_ADDSUB_W(rs1, rs2, rd, PAAS_WX) <->
  0b1 @ 0b0011 @ 0b01 @ rs2 @ rs1 @ 0b110 @ rd @ 0b0111011
mapping clause encdec = PEXT_ADDSUB_W(rs1, rs2, rd, PASA_WX) <->
  0b1 @ 0b0011 @ 0b11 @ rs2 @ rs1 @ 0b110 @ rd @ 0b0111011

function clause execute (PEXT_ADDSUB_W(rs1, rs2, rd, op)) = {
  let rs1_val = X(rs1);
  let rs2_val = X(rs2);
  var result : xlenbits = zeros();
  let rs1_halfword_even = slice(rs1_val, 0, 32);
  let rs2_halfword_even = slice(rs2_val, 0, 32);
  let rs1_halfword_odd = slice(rs1_val, 32, 32);
  let rs2_halfword_odd = slice(rs2_val, 32, 32);
  result = match op {
    PAS_WX => (rs1_halfword_odd + rs2_halfword_even) @ (rs1_halfword_even - rs2_halfword_odd),
    PSA_WX => (rs1_halfword_odd - rs2_halfword_even) @ (rs1_halfword_even + rs2_halfword_odd),
    PSAS_WX => sadd(rs1_halfword_odd, rs2_halfword_even) @ ssub(rs1_halfword_even, rs2_halfword_odd),
    PSSA_WX => ssub(rs1_halfword_odd, rs2_halfword_even) @ sadd(rs1_halfword_even, rs2_halfword_odd),
    PAAS_WX => aadd(rs1_halfword_odd, rs2_halfword_even) @ asub(rs1_halfword_even, rs2_halfword_odd),
    PASA_WX => asub(rs1_halfword_odd, rs2_halfword_even) @ aadd(rs1_halfword_even, rs2_halfword_odd)
  };
  X(rd) = result;
  RETIRE_SUCCESS
}

mapping p_addsub_w_mapping : p_addsub_w <-> string = {
  PAS_WX <-> "pas.wx",
  PSA_WX <-> "psa.wx",
  PSAS_WX <-> "psas.wx",
  PSSA_WX <-> "pssa.wx",
  PAAS_WX <-> "paas.wx",
  PASA_WX <-> "pasa.wx"
}

mapping clause assembly = PEXT_ADDSUB_W(rs1, rs2, rd, p_inst)
  <-> p_addsub_w_mapping(p_inst) ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)
