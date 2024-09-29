union clause ast = PEXT_SHIFT_LEFT_W_RV32 : (bits(5), regidx, regidx, pshift_left_w_rv32)

mapping clause encdec = PEXT_SHIFT_LEFT_W_RV32(imm5, rs1, rd, SSLAI) <->
  0b1 @ 0b101 @ 0b0 @ 0b01 @ imm5 @ rs1 @ 0b010 @ rd @ 0b0011011

function clause execute (PEXT_SHIFT_LEFT_W_RV32(imm5, rs1, rd, op)) = {
  let rs1_val = X(rs1);
  let sa : bits(8) = EXTZ(imm5);
  X(rd) = sat_shift_left_arith(rs1_val, sa);
  RETIRE_SUCCESS
}

mapping p_shift_w_rv32_mapping : pshift_left_w_rv32 <-> string = {
  SSLAI <-> "sslai"
}

mapping clause assembly = PEXT_SHIFT_LEFT_W_RV32(imm5, rs1, rd, p_inst)
  <-> p_shift_w_rv32_mapping(p_inst) ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ hex_bits_5(imm5)