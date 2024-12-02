union clause ast = PEXT_PACK_H : (regidx, regidx, regidx, p_pack_h)

mapping clause encdec = PEXT_PACK_H(rs1, rs2, rd, PPACK_H) <->
  0b1 @ 0b000 @ 0b0 @ 0b00 @ rs2 @ rs1 @ 0b100 @ rd @ 0b0111011
mapping clause encdec = PEXT_PACK_H(rs1, rs2, rd, PPACKBT_H) <->
  0b1 @ 0b001 @ 0b0 @ 0b00 @ rs2 @ rs1 @ 0b100 @ rd @ 0b0111011
mapping clause encdec = PEXT_PACK_H(rs1, rs2, rd, PPACKTB_H) <->
  0b1 @ 0b010 @ 0b0 @ 0b00 @ rs2 @ rs1 @ 0b100 @ rd @ 0b0111011
mapping clause encdec = PEXT_PACK_H(rs1, rs2, rd, PPACKT_H) <->
  0b1 @ 0b011 @ 0b0 @ 0b00 @ rs2 @ rs1 @ 0b100 @ rd @ 0b0111011

function clause execute (PEXT_PACK_H(rs1, rs2, rd, op)) = {
  let rs1_val = X(rs1);
  let rs2_val = X(rs2);
  var result : xlenbits = zeros();
  foreach (i from 0 to (sizeof(xlen) - 16) by 16) {
    let rs1_byte_even = slice(rs1_val, i, 8);
    let rs2_byte_even = slice(rs2_val, i, 8);
    let rs1_byte_odd = slice(rs1_val, i + 8, 8);
    let rs2_byte_odd = slice(rs2_val, i + 8, 8);
    result[(i+15)..i] = match op {
      PPACK_H => rs2_byte_even @ rs1_byte_even,
      PPACKBT_H => rs2_byte_odd @ rs1_byte_even,
      PPACKTB_H => rs2_byte_even @ rs1_byte_odd,
      PPACKT_H => rs2_byte_odd @ rs1_byte_odd
    };
  };
  X(rd) = result;
  RETIRE_SUCCESS
}

mapping p_pack_h_mapping : p_pack_h <-> string = {
  PPACK_H <-> "ppack.h",
  PPACKBT_H <-> "ppackbt.h",
  PPACKTB_H <-> "ppacktb.h",
  PPACKT_H <-> "ppackt.h"
}

mapping clause assembly = PEXT_PACK_H(rs1, rs2, rd, p_inst)
  <-> p_pack_h_mapping(p_inst) ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)

/* ****************************************************************** */

union clause ast = PEXT_PACK_W : (regidx, regidx, regidx, p_pack_w)

mapping clause encdec = PEXT_PACK_W(rs1, rs2, rd, PPACK_W) if sizeof(xlen) == 64 <->
  0b1 @ 0b000 @ 0b0 @ 0b01 @ rs2 @ rs1 @ 0b100 @ rd @ 0b0111011 if sizeof(xlen) == 64
mapping clause encdec = PEXT_PACK_W(rs1, rs2, rd, PPACKBT_W) if sizeof(xlen) == 64 <->
  0b1 @ 0b001 @ 0b0 @ 0b01 @ rs2 @ rs1 @ 0b100 @ rd @ 0b0111011 if sizeof(xlen) == 64
mapping clause encdec = PEXT_PACK_W(rs1, rs2, rd, PPACKTB_W) if sizeof(xlen) == 64 <->
  0b1 @ 0b010 @ 0b0 @ 0b01 @ rs2 @ rs1 @ 0b100 @ rd @ 0b0111011 if sizeof(xlen) == 64
mapping clause encdec = PEXT_PACK_W(rs1, rs2, rd, PPACKT_W) if sizeof(xlen) == 64 <->
  0b1 @ 0b011 @ 0b0 @ 0b01 @ rs2 @ rs1 @ 0b100 @ rd @ 0b0111011 if sizeof(xlen) == 64

function clause execute (PEXT_PACK_W(rs1, rs2, rd, op)) = {
  let rs1_val = X(rs1);
  let rs2_val = X(rs2);
  var result : xlenbits = zeros();
  foreach (i from 0 to (sizeof(xlen) - 32) by 32) {
    let rs1_halfword_even = slice(rs1_val, i, 16);
    let rs2_halfword_even = slice(rs2_val, i, 16);
    let rs1_halfword_odd = slice(rs1_val, i + 16, 16);
    let rs2_halfword_odd = slice(rs2_val, i + 16, 16);
    result[(i+31)..i] = match op {
      PPACK_W => rs2_halfword_even @ rs1_halfword_even,
      PPACKBT_W => rs2_halfword_odd @ rs1_halfword_even,
      PPACKTB_W => rs2_halfword_even @ rs1_halfword_odd,
      PPACKT_W => rs2_halfword_odd @ rs1_halfword_odd
    };
  };
  X(rd) = result;
  RETIRE_SUCCESS
}

mapping p_pack_w_mapping : p_pack_w <-> string = {
  PPACK_W <-> "ppack.w",
  PPACKBT_W <-> "ppackbt.w",
  PPACKTB_W <-> "ppacktb.w",
  PPACKT_W <-> "ppackt.w"
}

mapping clause assembly = PEXT_PACK_W(rs1, rs2, rd, p_inst)
  <-> p_pack_w_mapping(p_inst) ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)
