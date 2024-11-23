union clause ast = PEXT_SUM_RV32 : (pregidx, regidx, regidx, p_sum_rv32)

mapping clause encdec = PEXT_SUM_RV32(rs1p, rs2, rd, PREDSUM_DH) <->
  0b0 @ 0b001 @ 0b1 @ 0b00 @ rs2 @ rs1p @ 0b0100 @ rd @ 0b0011011
mapping clause encdec = PEXT_SUM_RV32(rs1p, rs2, rd, PREDSUMU_DH) <->
  0b0 @ 0b011 @ 0b1 @ 0b00 @ rs2 @ rs1p @ 0b0100 @ rd @ 0b0011011

function clause execute (PEXT_SUM_RV32(rs1p, rs2, rd, op)) = {
  let rs1_val = X(rs1p @ 0b1) @ X(rs1p @ 0b0);
  var result : bits(32) = X(rs2);
  foreach (i from 0 to (64 - 16) by 16) {
    result = match op {
      PREDSUM_DH => result + EXTS(rs1_val[(i+15)..i]),
      PREDSUMU_DH => result + EXTZ(rs1_val[(i+15)..i])
    };
  };
  X(rd) = result;
  RETIRE_SUCCESS
}

mapping p_sum_rv32_mapping : p_sum_rv32 <-> string = {
  PREDSUM_DH <-> "predsum.dh",
  PREDSUMU_DH <-> "predsumu.dh"
}

mapping clause assembly = PEXT_SUM_RV32(rs1p, rs2, rd, p_inst)
  <-> p_sum_rv32_mapping(p_inst) ^ spc() ^ reg_name(rd) ^ sep() ^ preg_name(rs1p) ^ sep() ^ reg_name(rs2)

/* ****************************************************************** */

union clause ast = PEXT_NARROWING_SHIFT_CLIP_IMM_B : (bits(4), pregidx, regidx, p_narrowing_shift_clip_imm_b)

mapping clause encdec = PEXT_NARROWING_SHIFT_CLIP_IMM_B(imm4, rs1p, rd, PNSRLI_B) <->
  0b0 @ 0b000 @ 0b0 @ 0b001 @ imm4 @ rs1p @ 0b1100 @ rd @ 0b0011011
mapping clause encdec = PEXT_NARROWING_SHIFT_CLIP_IMM_B(imm4, rs1p, rd, PNCLIPIU_B) <->
  0b0 @ 0b010 @ 0b0 @ 0b001 @ imm4 @ rs1p @ 0b1100 @ rd @ 0b0011011
mapping clause encdec = PEXT_NARROWING_SHIFT_CLIP_IMM_B(imm4, rs1p, rd, PNCLIPRIU_B) <->
  0b0 @ 0b011 @ 0b0 @ 0b001 @ imm4 @ rs1p @ 0b1100 @ rd @ 0b0011011
mapping clause encdec = PEXT_NARROWING_SHIFT_CLIP_IMM_B(imm4, rs1p, rd, PNSRAI_B) <->
  0b0 @ 0b100 @ 0b0 @ 0b001 @ imm4 @ rs1p @ 0b1100 @ rd @ 0b0011011
mapping clause encdec = PEXT_NARROWING_SHIFT_CLIP_IMM_B(imm4, rs1p, rd, PNSRARI_B) <->
  0b0 @ 0b101 @ 0b0 @ 0b001 @ imm4 @ rs1p @ 0b1100 @ rd @ 0b0011011
mapping clause encdec = PEXT_NARROWING_SHIFT_CLIP_IMM_B(imm4, rs1p, rd, PNCLIPI_B) <->
  0b0 @ 0b110 @ 0b0 @ 0b001 @ imm4 @ rs1p @ 0b1100 @ rd @ 0b0011011
mapping clause encdec = PEXT_NARROWING_SHIFT_CLIP_IMM_B(imm4, rs1p, rd, PNCLIPRI_B) <->
  0b0 @ 0b111 @ 0b0 @ 0b001 @ imm4 @ rs1p @ 0b1100 @ rd @ 0b0011011

function clause execute (PEXT_NARROWING_SHIFT_CLIP_IMM_B(imm4, rs1p, rd, op)) = {
  let rs1_val = X(rs1p @ 0b1) @ X(rs1p @ 0b0);
  let sa : bits(8) = EXTZ(imm4);
  var result : bits(32) = zeros();
  foreach (i from 0 to (32 - 8) by 8) {
    result[(i+7)..i] = match op {
      PNSRLI_B => shift_right_logic(rs1_val[(2*i+15)..(2*i)], sa)[7..0],
      PNCLIPIU_B => nclipu(rs1_val[(2*i+15)..(2*i)], sa)[7..0],
      PNCLIPRIU_B => nclipru(rs1_val[(2*i+15)..(2*i)], sa)[7..0],
      PNSRAI_B => shift_right_arith(rs1_val[(2*i+15)..(2*i)], sa)[7..0],
      PNSRARI_B => shift_right_arith_rounding(rs1_val[(2*i+15)..(2*i)], sa)[7..0],
      PNCLIPI_B => nclips(rs1_val[(2*i+15)..(2*i)], sa)[7..0],
      PNCLIPRI_B => ncliprs(rs1_val[(2*i+15)..(2*i)], sa)[7..0]
    };
  };
  X(rd) = result;
  RETIRE_SUCCESS
}

mapping p_narrowing_shift_clip_imm_b_mapping : p_narrowing_shift_clip_imm_b <-> string = {
  PNSRLI_B <-> "pnsrli.b",
  PNCLIPIU_B <-> "pnclipiu.b",
  PNCLIPRIU_B <-> "pnclipriu.b",
  PNSRAI_B <-> "pnsrai.b",
  PNSRARI_B <-> "pnsrari.b",
  PNCLIPI_B <-> "pnclipi.b",
  PNCLIPRI_B <-> "pnclipri.b"
}

mapping clause assembly = PEXT_NARROWING_SHIFT_CLIP_IMM_B(imm4, rs1p, rd, p_inst)
  <-> p_narrowing_shift_clip_imm_b_mapping(p_inst) ^ spc() ^ reg_name(rd) ^ sep() ^ preg_name(rs1p) ^ sep() ^ hex_bits_4(imm4)

/* ****************************************************************** */

union clause ast = PEXT_NARROWING_SHIFT_CLIP_IMM_H : (bits(5), pregidx, regidx, p_narrowing_shift_clip_imm_h)

mapping clause encdec = PEXT_NARROWING_SHIFT_CLIP_IMM_H(imm5, rs1p, rd, PNSRLI_H) <->
  0b0 @ 0b000 @ 0b0 @ 0b01 @ imm5 @ rs1p @ 0b1100 @ rd @ 0b0011011
mapping clause encdec = PEXT_NARROWING_SHIFT_CLIP_IMM_H(imm5, rs1p, rd, PNCLIPIU_H) <->
  0b0 @ 0b010 @ 0b0 @ 0b01 @ imm5 @ rs1p @ 0b1100 @ rd @ 0b0011011
mapping clause encdec = PEXT_NARROWING_SHIFT_CLIP_IMM_H(imm5, rs1p, rd, PNCLIPRIU_H) <->
  0b0 @ 0b011 @ 0b0 @ 0b01 @ imm5 @ rs1p @ 0b1100 @ rd @ 0b0011011
mapping clause encdec = PEXT_NARROWING_SHIFT_CLIP_IMM_H(imm5, rs1p, rd, PNSRAI_H) <->
  0b0 @ 0b100 @ 0b0 @ 0b01 @ imm5 @ rs1p @ 0b1100 @ rd @ 0b0011011
mapping clause encdec = PEXT_NARROWING_SHIFT_CLIP_IMM_H(imm5, rs1p, rd, PNSRARI_H) <->
  0b0 @ 0b101 @ 0b0 @ 0b01 @ imm5 @ rs1p @ 0b1100 @ rd @ 0b0011011
mapping clause encdec = PEXT_NARROWING_SHIFT_CLIP_IMM_H(imm5, rs1p, rd, PNCLIPI_H) <->
  0b0 @ 0b110 @ 0b0 @ 0b01 @ imm5 @ rs1p @ 0b1100 @ rd @ 0b0011011
mapping clause encdec = PEXT_NARROWING_SHIFT_CLIP_IMM_H(imm5, rs1p, rd, PNCLIPRI_H) <->
  0b0 @ 0b111 @ 0b0 @ 0b01 @ imm5 @ rs1p @ 0b1100 @ rd @ 0b0011011

function clause execute (PEXT_NARROWING_SHIFT_CLIP_IMM_H(imm5, rs1p, rd, op)) = {
  let rs1_val = X(rs1p @ 0b1) @ X(rs1p @ 0b0);
  let sa : bits(8) = EXTZ(imm5);
  var result : bits(32) = zeros();
  foreach (i from 0 to (32 - 16) by 16) {
    result[(i+15)..i] = match op {
      PNSRLI_H => shift_right_logic(rs1_val[(2*i+31)..(2*i)], sa)[15..0],
      PNCLIPIU_H => nclipu(rs1_val[(2*i+31)..(2*i)], sa)[15..0],
      PNCLIPRIU_H => nclipru(rs1_val[(2*i+31)..(2*i)], sa)[15..0],
      PNSRAI_H => shift_right_arith(rs1_val[(2*i+31)..(2*i)], sa)[15..0],
      PNSRARI_H => shift_right_arith_rounding(rs1_val[(2*i+31)..(2*i)], sa)[15..0],
      PNCLIPI_H => nclips(rs1_val[(2*i+31)..(2*i)], sa)[15..0],
      PNCLIPRI_H => ncliprs(rs1_val[(2*i+31)..(2*i)], sa)[15..0]
    };
  };
  X(rd) = result;
  RETIRE_SUCCESS
}

mapping p_narrowing_shift_clip_imm_h_mapping : p_narrowing_shift_clip_imm_h <-> string = {
  PNSRLI_H <-> "pnsrli.h",
  PNCLIPIU_H <-> "pnclipiu.h",
  PNCLIPRIU_H <-> "pnclipriu.h",
  PNSRAI_H <-> "pnsrai.h",
  PNSRARI_H <-> "pnsrari.h",
  PNCLIPI_H <-> "pnclipi.h",
  PNCLIPRI_H <-> "pnclipri.h"
}

mapping clause assembly = PEXT_NARROWING_SHIFT_CLIP_IMM_H(imm5, rs1p, rd, p_inst)
  <-> p_narrowing_shift_clip_imm_h_mapping(p_inst) ^ spc() ^ reg_name(rd) ^ sep() ^ preg_name(rs1p) ^ sep() ^ hex_bits_5(imm5)

/* ****************************************************************** */

union clause ast = PEXT_NARROWING_SHIFT_CLIP_IMM_W : (bits(6), pregidx, regidx, p_narrowing_shift_clip_imm_w)

mapping clause encdec = PEXT_NARROWING_SHIFT_CLIP_IMM_W(imm6, rs1p, rd, NSRLI) <->
  0b0 @ 0b000 @ 0b0 @ 0b1 @ imm6 @ rs1p @ 0b1100 @ rd @ 0b0011011
mapping clause encdec = PEXT_NARROWING_SHIFT_CLIP_IMM_W(imm6, rs1p, rd, NCLIPIU) <->
  0b0 @ 0b010 @ 0b0 @ 0b1 @ imm6 @ rs1p @ 0b1100 @ rd @ 0b0011011
mapping clause encdec = PEXT_NARROWING_SHIFT_CLIP_IMM_W(imm6, rs1p, rd, NCLIPRIU) <->
  0b0 @ 0b011 @ 0b0 @ 0b1 @ imm6 @ rs1p @ 0b1100 @ rd @ 0b0011011
mapping clause encdec = PEXT_NARROWING_SHIFT_CLIP_IMM_W(imm6, rs1p, rd, NSRAI) <->
  0b0 @ 0b100 @ 0b0 @ 0b1 @ imm6 @ rs1p @ 0b1100 @ rd @ 0b0011011
mapping clause encdec = PEXT_NARROWING_SHIFT_CLIP_IMM_W(imm6, rs1p, rd, NSRARI) <->
  0b0 @ 0b101 @ 0b0 @ 0b1 @ imm6 @ rs1p @ 0b1100 @ rd @ 0b0011011
mapping clause encdec = PEXT_NARROWING_SHIFT_CLIP_IMM_W(imm6, rs1p, rd, NCLIPI) <->
  0b0 @ 0b110 @ 0b0 @ 0b1 @ imm6 @ rs1p @ 0b1100 @ rd @ 0b0011011
mapping clause encdec = PEXT_NARROWING_SHIFT_CLIP_IMM_W(imm6, rs1p, rd, NCLIPRI) <->
  0b0 @ 0b111 @ 0b0 @ 0b1 @ imm6 @ rs1p @ 0b1100 @ rd @ 0b0011011

function clause execute (PEXT_NARROWING_SHIFT_CLIP_IMM_W(imm6, rs1p, rd, op)) = {
  let rs1_val = X(rs1p @ 0b1) @ X(rs1p @ 0b0);
  let sa : bits(8) = EXTZ(imm6);
  var result : bits(32) = zeros();
  result = match op {
    NSRLI => shift_right_logic(rs1_val, sa)[31..0],
    NCLIPIU => nclipu(rs1_val, sa)[31..0],
    NCLIPRIU => nclipru(rs1_val, sa)[31..0],
    NSRAI => shift_right_arith(rs1_val, sa)[31..0],
    NSRARI => shift_right_arith_rounding(rs1_val, sa)[31..0],
    NCLIPI => nclips(rs1_val, sa)[31..0],
    NCLIPRI => ncliprs(rs1_val, sa)[31..0]
  };
  X(rd) = result;
  RETIRE_SUCCESS
}

mapping p_narrowing_shift_clip_imm_w_mapping : p_narrowing_shift_clip_imm_w <-> string = {
  NSRLI <-> "nsrli",
  NCLIPIU <-> "nclipiu",
  NCLIPRIU <-> "nclipriu",
  NSRAI <-> "nsrai",
  NSRARI <-> "nsrari",
  NCLIPI <-> "nclipi",
  NCLIPRI <-> "nclipri"
}

mapping clause assembly = PEXT_NARROWING_SHIFT_CLIP_IMM_W(imm6, rs1p, rd, p_inst)
  <-> p_narrowing_shift_clip_imm_w_mapping(p_inst) ^ spc() ^ reg_name(rd) ^ sep() ^ preg_name(rs1p) ^ sep() ^ hex_bits_6(imm6)

/* ****************************************************************** */

union clause ast = PEXT_NARROWING_SHIFT_CLIP_B : (regidx, pregidx, regidx, p_narrowing_shift_clip_b)

mapping clause encdec = PEXT_NARROWING_SHIFT_CLIP_B(rs2, rs1p, rd, PNSRL_B_B0) <->
  0b0 @ 0b000 @ 0b1 @ 0b00 @ rs2 @ rs1p @ 0b1100 @ rd @ 0b0011011
mapping clause encdec = PEXT_NARROWING_SHIFT_CLIP_B(rs2, rs1p, rd, PNCLIPU_B_B0) <->
  0b0 @ 0b010 @ 0b1 @ 0b00 @ rs2 @ rs1p @ 0b1100 @ rd @ 0b0011011
mapping clause encdec = PEXT_NARROWING_SHIFT_CLIP_B(rs2, rs1p, rd, PNCLIPRU_B_B0) <->
  0b0 @ 0b011 @ 0b1 @ 0b00 @ rs2 @ rs1p @ 0b1100 @ rd @ 0b0011011
mapping clause encdec = PEXT_NARROWING_SHIFT_CLIP_B(rs2, rs1p, rd, PNSRA_B_B0) <->
  0b0 @ 0b100 @ 0b1 @ 0b00 @ rs2 @ rs1p @ 0b1100 @ rd @ 0b0011011
mapping clause encdec = PEXT_NARROWING_SHIFT_CLIP_B(rs2, rs1p, rd, PNSRAR_B_B0) <->
  0b0 @ 0b101 @ 0b1 @ 0b00 @ rs2 @ rs1p @ 0b1100 @ rd @ 0b0011011
mapping clause encdec = PEXT_NARROWING_SHIFT_CLIP_B(rs2, rs1p, rd, PNCLIP_B_B0) <->
  0b0 @ 0b110 @ 0b1 @ 0b00 @ rs2 @ rs1p @ 0b1100 @ rd @ 0b0011011
mapping clause encdec = PEXT_NARROWING_SHIFT_CLIP_B(rs2, rs1p, rd, PNCLIPR_B_B0) <->
  0b0 @ 0b111 @ 0b1 @ 0b00 @ rs2 @ rs1p @ 0b1100 @ rd @ 0b0011011

function clause execute (PEXT_NARROWING_SHIFT_CLIP_B(rs2, rs1p, rd, op)) = {
  let rs1_val = X(rs1p @ 0b1) @ X(rs1p @ 0b0);
  let sa : bits(8) = EXTZ(X(rs2)[3..0]);
  var result : bits(32) = zeros();
  foreach (i from 0 to (32 - 8) by 8) {
    result[(i+7)..i] = match op {
      PNSRL_B_B0 => shift_right_logic(rs1_val[(2*i+15)..(2*i)], sa)[7..0],
      PNCLIPU_B_B0 => nclipu(rs1_val[(2*i+15)..(2*i)], sa)[7..0],
      PNCLIPRU_B_B0 => nclipru(rs1_val[(2*i+15)..(2*i)], sa)[7..0],
      PNSRA_B_B0 => shift_right_arith(rs1_val[(2*i+15)..(2*i)], sa)[7..0],
      PNSRAR_B_B0 => shift_right_arith_rounding(rs1_val[(2*i+15)..(2*i)], sa)[7..0],
      PNCLIP_B_B0 => nclips(rs1_val[(2*i+15)..(2*i)], sa)[7..0],
      PNCLIPR_B_B0 => ncliprs(rs1_val[(2*i+15)..(2*i)], sa)[7..0]
    };
  };
  X(rd) = result;
  RETIRE_SUCCESS
}

mapping p_narrowing_shift_clip_b_mapping : p_narrowing_shift_clip_b <-> string = {
  PNSRL_B_B0 <-> "pnsrl.b.b0",
  PNCLIPU_B_B0 <-> "pnclipu.b.b0",
  PNCLIPRU_B_B0 <-> "pnclipru.b.b0",
  PNSRA_B_B0 <-> "pnsra.b.b0",
  PNSRAR_B_B0 <-> "pnsrar.b.b0",
  PNCLIP_B_B0 <-> "pnclip.b.b0",
  PNCLIPR_B_B0 <-> "pnclipr.b.b0"
}

mapping clause assembly = PEXT_NARROWING_SHIFT_CLIP_B(rs2, rs1p, rd, p_inst)
  <-> p_narrowing_shift_clip_b_mapping(p_inst) ^ spc() ^ reg_name(rd) ^ sep() ^ preg_name(rs1p) ^ sep() ^ reg_name(rs2)

/* ****************************************************************** */

union clause ast = PEXT_NARROWING_SHIFT_CLIP_H : (regidx, pregidx, regidx, p_narrowing_shift_clip_h)

mapping clause encdec = PEXT_NARROWING_SHIFT_CLIP_H(rs2, rs1p, rd, PNSRL_H_H0) <->
  0b0 @ 0b000 @ 0b1 @ 0b01 @ rs2 @ rs1p @ 0b1100 @ rd @ 0b0011011
mapping clause encdec = PEXT_NARROWING_SHIFT_CLIP_H(rs2, rs1p, rd, PNCLIPU_H_H0) <->
  0b0 @ 0b010 @ 0b1 @ 0b01 @ rs2 @ rs1p @ 0b1100 @ rd @ 0b0011011
mapping clause encdec = PEXT_NARROWING_SHIFT_CLIP_H(rs2, rs1p, rd, PNCLIPRU_H_H0) <->
  0b0 @ 0b011 @ 0b1 @ 0b01 @ rs2 @ rs1p @ 0b1100 @ rd @ 0b0011011
mapping clause encdec = PEXT_NARROWING_SHIFT_CLIP_H(rs2, rs1p, rd, PNSRA_H_H0) <->
  0b0 @ 0b100 @ 0b1 @ 0b01 @ rs2 @ rs1p @ 0b1100 @ rd @ 0b0011011
mapping clause encdec = PEXT_NARROWING_SHIFT_CLIP_H(rs2, rs1p, rd, PNSRAR_H_H0) <->
  0b0 @ 0b101 @ 0b1 @ 0b01 @ rs2 @ rs1p @ 0b1100 @ rd @ 0b0011011
mapping clause encdec = PEXT_NARROWING_SHIFT_CLIP_H(rs2, rs1p, rd, PNCLIP_H_H0) <->
  0b0 @ 0b110 @ 0b1 @ 0b01 @ rs2 @ rs1p @ 0b1100 @ rd @ 0b0011011
mapping clause encdec = PEXT_NARROWING_SHIFT_CLIP_H(rs2, rs1p, rd, PNCLIPR_H_H0) <->
  0b0 @ 0b111 @ 0b1 @ 0b01 @ rs2 @ rs1p @ 0b1100 @ rd @ 0b0011011

function clause execute (PEXT_NARROWING_SHIFT_CLIP_H(rs2, rs1p, rd, op)) = {
  let rs1_val = X(rs1p @ 0b1) @ X(rs1p @ 0b0);
  let sa : bits(8) = EXTZ(X(rs2)[4..0]);
  var result : bits(32) = zeros();
  foreach (i from 0 to (32 - 16) by 16) {
    result[(i+15)..i] = match op {
      PNSRL_H_H0 => shift_right_logic(rs1_val[(2*i+31)..(2*i)], sa)[15..0],
      PNCLIPU_H_H0 => nclipu(rs1_val[(2*i+31)..(2*i)], sa)[15..0],
      PNCLIPRU_H_H0 => nclipru(rs1_val[(2*i+31)..(2*i)], sa)[15..0],
      PNSRA_H_H0 => shift_right_arith(rs1_val[(2*i+31)..(2*i)], sa)[15..0],
      PNSRAR_H_H0 => shift_right_arith_rounding(rs1_val[(2*i+31)..(2*i)], sa)[15..0],
      PNCLIP_H_H0 => nclips(rs1_val[(2*i+31)..(2*i)], sa)[15..0],
      PNCLIPR_H_H0 => ncliprs(rs1_val[(2*i+31)..(2*i)], sa)[15..0]
    };
  };
  X(rd) = result;
  RETIRE_SUCCESS
}

mapping p_narrowing_shift_clip_h_mapping : p_narrowing_shift_clip_h <-> string = {
  PNSRL_H_H0 <-> "pnsrl.h.h0",
  PNCLIPU_H_H0 <-> "pnclipu.h.h0",
  PNCLIPRU_H_H0 <-> "pnclipru.h.h0",
  PNSRA_H_H0 <-> "pnsra.h.h0",
  PNSRAR_H_H0 <-> "pnsrar.h.h0",
  PNCLIP_H_H0 <-> "pnclip.h.h0",
  PNCLIPR_H_H0 <-> "pnclipr.h.h0"
}

mapping clause assembly = PEXT_NARROWING_SHIFT_CLIP_H(rs2, rs1p, rd, p_inst)
  <-> p_narrowing_shift_clip_h_mapping(p_inst) ^ spc() ^ reg_name(rd) ^ sep() ^ preg_name(rs1p) ^ sep() ^ reg_name(rs2)

/* ****************************************************************** */

union clause ast = PEXT_NARROWING_SHIFT_CLIP_W : (regidx, pregidx, regidx, p_narrowing_shift_clip_w)

mapping clause encdec = PEXT_NARROWING_SHIFT_CLIP_W(rs2, rs1p, rd, NSRL) <->
  0b0 @ 0b000 @ 0b1 @ 0b11 @ rs2 @ rs1p @ 0b1100 @ rd @ 0b0011011
mapping clause encdec = PEXT_NARROWING_SHIFT_CLIP_W(rs2, rs1p, rd, NCLIPU) <->
  0b0 @ 0b010 @ 0b1 @ 0b11 @ rs2 @ rs1p @ 0b1100 @ rd @ 0b0011011
mapping clause encdec = PEXT_NARROWING_SHIFT_CLIP_W(rs2, rs1p, rd, NCLIPRU) <->
  0b0 @ 0b011 @ 0b1 @ 0b11 @ rs2 @ rs1p @ 0b1100 @ rd @ 0b0011011
mapping clause encdec = PEXT_NARROWING_SHIFT_CLIP_W(rs2, rs1p, rd, NSRA) <->
  0b0 @ 0b100 @ 0b1 @ 0b11 @ rs2 @ rs1p @ 0b1100 @ rd @ 0b0011011
mapping clause encdec = PEXT_NARROWING_SHIFT_CLIP_W(rs2, rs1p, rd, NSRAR) <->
  0b0 @ 0b101 @ 0b1 @ 0b11 @ rs2 @ rs1p @ 0b1100 @ rd @ 0b0011011
mapping clause encdec = PEXT_NARROWING_SHIFT_CLIP_W(rs2, rs1p, rd, NCLIP) <->
  0b0 @ 0b110 @ 0b1 @ 0b11 @ rs2 @ rs1p @ 0b1100 @ rd @ 0b0011011
mapping clause encdec = PEXT_NARROWING_SHIFT_CLIP_W(rs2, rs1p, rd, NCLIPR) <->
  0b0 @ 0b111 @ 0b1 @ 0b11 @ rs2 @ rs1p @ 0b1100 @ rd @ 0b0011011

function clause execute (PEXT_NARROWING_SHIFT_CLIP_W(rs2, rs1p, rd, op)) = {
  let rs1_val = X(rs1p @ 0b1) @ X(rs1p @ 0b0);
  let sa : bits(8) = EXTZ(X(rs2)[5..0]);
  var result : bits(32) = zeros();
  result = match op {
    NSRL => shift_right_logic(rs1_val, sa)[31..0],
    NCLIPU => nclipu(rs1_val, sa)[31..0],
    NCLIPRU => nclipru(rs1_val, sa)[31..0],
    NSRA => shift_right_arith(rs1_val, sa)[31..0],
    NSRAR => shift_right_arith_rounding(rs1_val, sa)[31..0],
    NCLIP => nclips(rs1_val, sa)[31..0],
    NCLIPR => ncliprs(rs1_val, sa)[31..0]
  };
  X(rd) = result;
  RETIRE_SUCCESS
}

mapping p_narrowing_shift_clip_w_mapping : p_narrowing_shift_clip_w <-> string = {
  NSRL <-> "nsrl",
  NCLIPU <-> "nclipu",
  NCLIPRU <-> "nclipru",
  NSRA <-> "nsra",
  NSRAR <-> "nsrar",
  NCLIP <-> "nclip",
  NCLIPR <-> "nclipr"
}

mapping clause assembly = PEXT_NARROWING_SHIFT_CLIP_W(rs2, rs1p, rd, p_inst)
  <-> p_narrowing_shift_clip_w_mapping(p_inst) ^ spc() ^ reg_name(rd) ^ sep() ^ preg_name(rs1p) ^ sep() ^ reg_name(rs2)
