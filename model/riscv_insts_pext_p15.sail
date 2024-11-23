union clause ast = PEXT_MUL2HORIZON_H : (regidx, regidx, regidx, p_mul2horizon_h)

mapping clause encdec = PEXT_MUL2HORIZON_H(rs1, rs2, rd, PM2ADD_H) <->
  0b1 @ 0b0000 @ 0b00 @ rs2 @ rs1 @ 0b101 @ rd @ 0b0111011
mapping clause encdec = PEXT_MUL2HORIZON_H(rs1, rs2, rd, PM2ADDA_H) <->
  0b1 @ 0b0001 @ 0b00 @ rs2 @ rs1 @ 0b101 @ rd @ 0b0111011
mapping clause encdec = PEXT_MUL2HORIZON_H(rs1, rs2, rd, PM2ADD_HX) <->
  0b1 @ 0b0010 @ 0b00 @ rs2 @ rs1 @ 0b101 @ rd @ 0b0111011
mapping clause encdec = PEXT_MUL2HORIZON_H(rs1, rs2, rd, PM2ADDA_HX) <->
  0b1 @ 0b0011 @ 0b00 @ rs2 @ rs1 @ 0b101 @ rd @ 0b0111011
mapping clause encdec = PEXT_MUL2HORIZON_H(rs1, rs2, rd, PM2ADDU_H) <->
  0b1 @ 0b0100 @ 0b00 @ rs2 @ rs1 @ 0b101 @ rd @ 0b0111011
mapping clause encdec = PEXT_MUL2HORIZON_H(rs1, rs2, rd, PM2ADDAU_H) <->
  0b1 @ 0b0101 @ 0b00 @ rs2 @ rs1 @ 0b101 @ rd @ 0b0111011
mapping clause encdec = PEXT_MUL2HORIZON_H(rs1, rs2, rd, PM2ADDSU_H) <->
  0b1 @ 0b1100 @ 0b00 @ rs2 @ rs1 @ 0b101 @ rd @ 0b0111011
mapping clause encdec = PEXT_MUL2HORIZON_H(rs1, rs2, rd, PM2ADDASU_H) <->
  0b1 @ 0b1101 @ 0b00 @ rs2 @ rs1 @ 0b101 @ rd @ 0b0111011
mapping clause encdec = PEXT_MUL2HORIZON_H(rs1, rs2, rd, PM2SADD_H) <->
  0b1 @ 0b1000 @ 0b10 @ rs2 @ rs1 @ 0b101 @ rd @ 0b0111011
mapping clause encdec = PEXT_MUL2HORIZON_H(rs1, rs2, rd, PM2SADD_HX) <->
  0b1 @ 0b1010 @ 0b10 @ rs2 @ rs1 @ 0b101 @ rd @ 0b0111011
mapping clause encdec = PEXT_MUL2HORIZON_H(rs1, rs2, rd, PMQ2ADD_H) <->
  0b1 @ 0b0110 @ 0b00 @ rs2 @ rs1 @ 0b101 @ rd @ 0b0111011
mapping clause encdec = PEXT_MUL2HORIZON_H(rs1, rs2, rd, PMQ2ADDA_H) <->
  0b1 @ 0b0111 @ 0b00 @ rs2 @ rs1 @ 0b101 @ rd @ 0b0111011
mapping clause encdec = PEXT_MUL2HORIZON_H(rs1, rs2, rd, PMQR2ADD_H) <->
  0b1 @ 0b0110 @ 0b10 @ rs2 @ rs1 @ 0b101 @ rd @ 0b0111011
mapping clause encdec = PEXT_MUL2HORIZON_H(rs1, rs2, rd, PMQR2ADDA_H) <->
  0b1 @ 0b0111 @ 0b10 @ rs2 @ rs1 @ 0b101 @ rd @ 0b0111011
mapping clause encdec = PEXT_MUL2HORIZON_H(rs1, rs2, rd, PM2SUB_H) <->
  0b1 @ 0b1000 @ 0b00 @ rs2 @ rs1 @ 0b101 @ rd @ 0b0111011
mapping clause encdec = PEXT_MUL2HORIZON_H(rs1, rs2, rd, PM2SUBA_H) <->
  0b1 @ 0b1001 @ 0b00 @ rs2 @ rs1 @ 0b101 @ rd @ 0b0111011
mapping clause encdec = PEXT_MUL2HORIZON_H(rs1, rs2, rd, PM2SUB_HX) <->
  0b1 @ 0b1010 @ 0b00 @ rs2 @ rs1 @ 0b101 @ rd @ 0b0111011
mapping clause encdec = PEXT_MUL2HORIZON_H(rs1, rs2, rd, PM2SUBA_HX) <->
  0b1 @ 0b1011 @ 0b00 @ rs2 @ rs1 @ 0b101 @ rd @ 0b0111011

function clause execute (PEXT_MUL2HORIZON_H(rs1, rs2, rd, op)) = {
  let rs1_val = X(rs1);
  let rs2_val = X(rs2);
  let rd_val = X(rd);
  var result : xlenbits = zeros();
  foreach (i from 0 to (sizeof(xlen) - 32) by 32) {
    let rs1_halfword_even = slice(rs1_val, i, 16);
    let rs2_halfword_even = slice(rs2_val, i, 16);
    let rs1_halfword_odd = slice(rs1_val, i + 16, 16);
    let rs2_halfword_odd = slice(rs2_val, i + 16, 16);
    result[(i+31)..i] = match op {
      PM2ADD_H => muls(rs1_halfword_odd, rs2_halfword_odd) + muls(rs1_halfword_even, rs2_halfword_even),
      PM2ADDA_H => rd_val[(i+31)..i] + muls(rs1_halfword_odd, rs2_halfword_odd) + muls(rs1_halfword_even, rs2_halfword_even),
      PM2ADD_HX => muls(rs1_halfword_odd, rs2_halfword_even) + muls(rs1_halfword_even, rs2_halfword_odd),
      PM2ADDA_HX => rd_val[(i+31)..i] + muls(rs1_halfword_odd, rs2_halfword_even) + muls(rs1_halfword_even, rs2_halfword_odd),
      PM2ADDU_H => mulu(rs1_halfword_odd, rs2_halfword_odd) + mulu(rs1_halfword_even, rs2_halfword_even),
      PM2ADDAU_H => rd_val[(i+31)..i] + mulu(rs1_halfword_odd, rs2_halfword_odd) + mulu(rs1_halfword_even, rs2_halfword_even),
      PM2ADDSU_H => mulsu(rs1_halfword_odd, rs2_halfword_odd) + mulsu(rs1_halfword_even, rs2_halfword_even),
      PM2ADDASU_H => rd_val[(i+31)..i] + mulsu(rs1_halfword_odd, rs2_halfword_odd) + mulsu(rs1_halfword_even, rs2_halfword_even),
      PM2SADD_H => sadd(muls(rs1_halfword_odd, rs2_halfword_odd), muls(rs1_halfword_even, rs2_halfword_even)),
      PM2SADD_HX => sadd(muls(rs1_halfword_odd, rs2_halfword_even), muls(rs1_halfword_even, rs2_halfword_odd)),
      PMQ2ADD_H => mulq(rs1_halfword_odd, rs2_halfword_odd) + mulq(rs1_halfword_even, rs2_halfword_even),
      PMQ2ADDA_H => rd_val[(i+31)..i] + mulq(rs1_halfword_odd, rs2_halfword_odd) + mulq(rs1_halfword_even, rs2_halfword_even),
      PMQR2ADD_H => mulqr(rs1_halfword_odd, rs2_halfword_odd) + mulqr(rs1_halfword_even, rs2_halfword_even),
      PMQR2ADDA_H => rd_val[(i+31)..i] + mulqr(rs1_halfword_odd, rs2_halfword_odd) + mulqr(rs1_halfword_even, rs2_halfword_even),
      PM2SUB_H => muls(rs1_halfword_odd, rs2_halfword_odd) - muls(rs1_halfword_even, rs2_halfword_even),
      PM2SUBA_H => rd_val[(i+31)..i] + muls(rs1_halfword_odd, rs2_halfword_odd) - muls(rs1_halfword_even, rs2_halfword_even),
      PM2SUB_HX => muls(rs1_halfword_odd, rs2_halfword_even) - muls(rs1_halfword_even, rs2_halfword_odd),
      PM2SUBA_HX => rd_val[(i+31)..i] + muls(rs1_halfword_odd, rs2_halfword_even) - muls(rs1_halfword_even, rs2_halfword_odd)
    };
  };
  X(rd) = result;
  RETIRE_SUCCESS
}

mapping p_mul2horizon_h_mapping : p_mul2horizon_h <-> string = {
  PM2ADD_H <-> "pm2add.h",
  PM2ADDA_H <-> "pm2adda.h",
  PM2ADD_HX <-> "pm2add.hx",
  PM2ADDA_HX <-> "pm2adda.hx",
  PM2ADDU_H <-> "pm2addu.h",
  PM2ADDAU_H <-> "pm2addau.h",
  PM2ADDSU_H <-> "pm2addsu.h",
  PM2ADDASU_H <-> "pm2addasu.h",
  PM2SADD_H <-> "pm2sadd.h",
  PM2SADD_HX <-> "pm2sadd.hx",
  PMQ2ADD_H <-> "pmq2add.h",
  PMQ2ADDA_H <-> "pmq2adda.h",
  PMQR2ADD_H <-> "pmqr2add.h",
  PMQR2ADDA_H <-> "pmqr2adda.h",
  PM2SUB_H <-> "pm2sub.h",
  PM2SUBA_H <-> "pm2suba.h",
  PM2SUB_HX <-> "pm2sub.hx",
  PM2SUBA_HX <-> "pm2suba.hx"
}

mapping clause assembly = PEXT_MUL2HORIZON_H(rs1, rs2, rd, p_inst)
  <-> p_mul2horizon_h_mapping(p_inst) ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)

/* ****************************************************************** */

union clause ast = PEXT_MUL4HORIZON_B : (regidx, regidx, regidx, p_mul4horizon_b)

mapping clause encdec = PEXT_MUL4HORIZON_B(rs1, rs2, rd, PM4ADD_B) <->
  0b1 @ 0b0000 @ 0b10 @ rs2 @ rs1 @ 0b101 @ rd @ 0b0111011
mapping clause encdec = PEXT_MUL4HORIZON_B(rs1, rs2, rd, PM4ADDA_B) <->
  0b1 @ 0b0001 @ 0b10 @ rs2 @ rs1 @ 0b101 @ rd @ 0b0111011
mapping clause encdec = PEXT_MUL4HORIZON_B(rs1, rs2, rd, PM4ADDU_B) <->
  0b1 @ 0b0100 @ 0b10 @ rs2 @ rs1 @ 0b101 @ rd @ 0b0111011
mapping clause encdec = PEXT_MUL4HORIZON_B(rs1, rs2, rd, PM4ADDAU_B) <->
  0b1 @ 0b0101 @ 0b10 @ rs2 @ rs1 @ 0b101 @ rd @ 0b0111011
mapping clause encdec = PEXT_MUL4HORIZON_B(rs1, rs2, rd, PM4ADDSU_B) <->
  0b1 @ 0b1100 @ 0b10 @ rs2 @ rs1 @ 0b101 @ rd @ 0b0111011
mapping clause encdec = PEXT_MUL4HORIZON_B(rs1, rs2, rd, PM4ADDASU_B) <->
  0b1 @ 0b1101 @ 0b10 @ rs2 @ rs1 @ 0b101 @ rd @ 0b0111011

function clause execute (PEXT_MUL4HORIZON_B(rs1, rs2, rd, op)) = {
  let rs1_val = X(rs1);
  let rs2_val = X(rs2);
  let rd_val = X(rd);
  var result : xlenbits = match op {
    PM4ADD_B => zeros(),
    PM4ADDA_B => rd_val,
    PM4ADDU_B => zeros(),
    PM4ADDAU_B => rd_val,
    PM4ADDSU_B => zeros(),
    PM4ADDASU_B => rd_val
  };
  foreach (i from 0 to (sizeof(xlen) - 32) by 32) {
    foreach (j from i to (i + 24) by 8) {
      result[(i+31)..i] = match op {
        PM4ADD_B => result[(i+31)..i] + EXTS(muls(rs1_val[(j+7)..j], rs2_val[(j+7)..j])),
        PM4ADDA_B => result[(i+31)..i] + EXTS(muls(rs1_val[(j+7)..j], rs2_val[(j+7)..j])),
        PM4ADDU_B => result[(i+31)..i] + EXTZ(mulu(rs1_val[(j+7)..j], rs2_val[(j+7)..j])),
        PM4ADDAU_B => result[(i+31)..i] + EXTZ(mulu(rs1_val[(j+7)..j], rs2_val[(j+7)..j])),
        PM4ADDSU_B => result[(i+31)..i] + EXTS(mulsu(rs1_val[(j+7)..j], rs2_val[(j+7)..j])),
        PM4ADDASU_B => result[(i+31)..i] + EXTS(mulsu(rs1_val[(j+7)..j], rs2_val[(j+7)..j]))
      };
    };
  };
  X(rd) = result;
  RETIRE_SUCCESS
}

mapping p_mul4horizon_b_mapping : p_mul4horizon_b <-> string = {
  PM4ADD_B <-> "pm4add.b",
  PM4ADDA_B <-> "pm4adda.b",
  PM4ADDU_B <-> "pm4addu.b",
  PM4ADDAU_B <-> "pm4addau.b",
  PM4ADDSU_B <-> "pm4addsu.b",
  PM4ADDASU_B <-> "pm4addasu.b"
}

mapping clause assembly = PEXT_MUL4HORIZON_B(rs1, rs2, rd, p_inst)
  <-> p_mul4horizon_b_mapping(p_inst) ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)
