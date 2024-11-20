union clause ast = PEXT_SHIFT_SAT : (bits(5), regidx, regidx, p_shift_sat)

mapping clause encdec = PEXT_SHIFT_SAT(imm5, rs1, rd, USATI) <->
  0b1 @ 0b010 @ 0b0 @ 0b01 @ imm5 @ rs1 @ 0b100 @ rd @ 0b0011011
mapping clause encdec = PEXT_SHIFT_SAT(imm5, rs1, rd, SRARI) <->
  0b1 @ 0b101 @ 0b0 @ 0b01 @ imm5 @ rs1 @ 0b100 @ rd @ 0b0011011
mapping clause encdec = PEXT_SHIFT_SAT(imm5, rs1, rd, SATI) <->
  0b1 @ 0b110 @ 0b0 @ 0b01 @ imm5 @ rs1 @ 0b100 @ rd @ 0b0011011

function clause execute (PEXT_SHIFT_SAT(imm5, rs1, rd, op)) = {
  let rs1_val = X(rs1);
  let sa : bits(8) = EXTZ(imm5);
  var result : xlenbits = zeros();
  result = match op {
    USATI =>
      let maxval : bits(32) = ~(0xFFFFFFFF << sa) in
      if (rs1_val <_s 0x00000000) then 0x00000000
      else if (rs1_val >_s maxval) then maxval else rs1_val,
    SRARI => shift_right_arith_rounding(rs1_val, sa),
    SATI =>
      let minval : bits(32) = 0xFFFFFFFF << sa in
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

mapping clause assembly = PEXT_SHIFT_SAT(imm5, rs1, rd, p_inst)
  <-> p_shift_sat_mapping(p_inst) ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ hex_bits_5(imm5)

/* ****************************************************************** */

union clause ast = PEXT_PACK : (regidx, regidx, regidx, p_pack)

mapping clause encdec = PEXT_PACK(rs1, rs2, rd, PACKBT) <->
  0b1 @ 0b001 @ 0b0 @ 0b01 @ rs2 @ rs1 @ 0b100 @ rd @ 0b0111011
mapping clause encdec = PEXT_PACK(rs1, rs2, rd, PACKTB) <->
  0b1 @ 0b010 @ 0b0 @ 0b01 @ rs2 @ rs1 @ 0b100 @ rd @ 0b0111011
mapping clause encdec = PEXT_PACK(rs1, rs2, rd, PACKT) <->
  0b1 @ 0b011 @ 0b0 @ 0b01 @ rs2 @ rs1 @ 0b100 @ rd @ 0b0111011

function clause execute (PEXT_PACK(rs1, rs2, rd, op)) = {
  let rs1_val = X(rs1);
  let rs2_val = X(rs2);
  var result : xlenbits = zeros();
  result = match op {
    PACKBT => rs2_val[31..16] @ rs1_val[15..0],
    PACKTB => rs2_val[15..0] @ rs1_val[31..16],
    PACKT => rs2_val[31..16] @ rs1_val[31..16]
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
