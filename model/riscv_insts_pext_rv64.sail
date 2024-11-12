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