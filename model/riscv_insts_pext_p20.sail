union clause ast = PEXT_SUM_RV32 : (pregidx, regidx, regidx, p_sum_rv32)

mapping clause encdec = PEXT_SUM_RV32(rs1p, rs2, rd, PREDSUM_DHS) <->
  0b0 @ 0b001 @ 0b1 @ 0b00 @ rs2 @ rs1p @ 0b0100 @ rd @ 0b0011011
mapping clause encdec = PEXT_SUM_RV32(rs1p, rs2, rd, PREDSUMU_DHS) <->
  0b0 @ 0b011 @ 0b1 @ 0b00 @ rs2 @ rs1p @ 0b0100 @ rd @ 0b0011011

function clause execute (PEXT_SUM_RV32(rs1p, rs2, rd, op)) = {
  let rs1_val = X(rs1p @ 0b1) @ X(rs1p @ 0b0);
  var result : bits(32) = X(rs2);
  foreach (i from 0 to (64 - 16) by 16) {
    result = match op {
      PREDSUM_DHS => result + EXTS(rs1_val[(i+15)..i]),
      PREDSUMU_DHS => result + EXTZ(rs1_val[(i+15)..i])
    };
  };
  X(rd) = result;
  RETIRE_SUCCESS
}

mapping p_sum_rv32_mapping : p_sum_rv32 <-> string = {
  PREDSUM_DHS <-> "predsum.dhs",
  PREDSUMU_DHS <-> "predsumu.dhs"
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

mapping clause encdec = PEXT_NARROWING_SHIFT_CLIP_B(rs2, rs1p, rd, PNSRL_BS) <->
  0b0 @ 0b000 @ 0b1 @ 0b00 @ rs2 @ rs1p @ 0b1100 @ rd @ 0b0011011
mapping clause encdec = PEXT_NARROWING_SHIFT_CLIP_B(rs2, rs1p, rd, PNCLIPU_BS) <->
  0b0 @ 0b010 @ 0b1 @ 0b00 @ rs2 @ rs1p @ 0b1100 @ rd @ 0b0011011
mapping clause encdec = PEXT_NARROWING_SHIFT_CLIP_B(rs2, rs1p, rd, PNCLIPRU_BS) <->
  0b0 @ 0b011 @ 0b1 @ 0b00 @ rs2 @ rs1p @ 0b1100 @ rd @ 0b0011011
mapping clause encdec = PEXT_NARROWING_SHIFT_CLIP_B(rs2, rs1p, rd, PNSRA_BS) <->
  0b0 @ 0b100 @ 0b1 @ 0b00 @ rs2 @ rs1p @ 0b1100 @ rd @ 0b0011011
mapping clause encdec = PEXT_NARROWING_SHIFT_CLIP_B(rs2, rs1p, rd, PNSRAR_BS) <->
  0b0 @ 0b101 @ 0b1 @ 0b00 @ rs2 @ rs1p @ 0b1100 @ rd @ 0b0011011
mapping clause encdec = PEXT_NARROWING_SHIFT_CLIP_B(rs2, rs1p, rd, PNCLIP_BS) <->
  0b0 @ 0b110 @ 0b1 @ 0b00 @ rs2 @ rs1p @ 0b1100 @ rd @ 0b0011011
mapping clause encdec = PEXT_NARROWING_SHIFT_CLIP_B(rs2, rs1p, rd, PNCLIPR_BS) <->
  0b0 @ 0b111 @ 0b1 @ 0b00 @ rs2 @ rs1p @ 0b1100 @ rd @ 0b0011011

function clause execute (PEXT_NARROWING_SHIFT_CLIP_B(rs2, rs1p, rd, op)) = {
  let rs1_val = X(rs1p @ 0b1) @ X(rs1p @ 0b0);
  let sa : bits(8) = EXTZ(X(rs2)[3..0]);
  var result : bits(32) = zeros();
  foreach (i from 0 to (32 - 8) by 8) {
    result[(i+7)..i] = match op {
      PNSRL_BS => shift_right_logic(rs1_val[(2*i+15)..(2*i)], sa)[7..0],
      PNCLIPU_BS => nclipu(rs1_val[(2*i+15)..(2*i)], sa)[7..0],
      PNCLIPRU_BS => nclipru(rs1_val[(2*i+15)..(2*i)], sa)[7..0],
      PNSRA_BS => shift_right_arith(rs1_val[(2*i+15)..(2*i)], sa)[7..0],
      PNSRAR_BS => shift_right_arith_rounding(rs1_val[(2*i+15)..(2*i)], sa)[7..0],
      PNCLIP_BS => nclips(rs1_val[(2*i+15)..(2*i)], sa)[7..0],
      PNCLIPR_BS => ncliprs(rs1_val[(2*i+15)..(2*i)], sa)[7..0]
    };
  };
  X(rd) = result;
  RETIRE_SUCCESS
}

mapping p_narrowing_shift_clip_b_mapping : p_narrowing_shift_clip_b <-> string = {
  PNSRL_BS <-> "pnsrl.bs",
  PNCLIPU_BS <-> "pnclipu.bs",
  PNCLIPRU_BS <-> "pnclipru.bs",
  PNSRA_BS <-> "pnsra.bs",
  PNSRAR_BS <-> "pnsrar.bs",
  PNCLIP_BS <-> "pnclip.bs",
  PNCLIPR_BS <-> "pnclipr.bs"
}

mapping clause assembly = PEXT_NARROWING_SHIFT_CLIP_B(rs2, rs1p, rd, p_inst)
  <-> p_narrowing_shift_clip_b_mapping(p_inst) ^ spc() ^ reg_name(rd) ^ sep() ^ preg_name(rs1p) ^ sep() ^ reg_name(rs2)

/* ****************************************************************** */

union clause ast = PEXT_NARROWING_SHIFT_CLIP_H : (regidx, pregidx, regidx, p_narrowing_shift_clip_h)

mapping clause encdec = PEXT_NARROWING_SHIFT_CLIP_H(rs2, rs1p, rd, PNSRL_HS) <->
  0b0 @ 0b000 @ 0b1 @ 0b01 @ rs2 @ rs1p @ 0b1100 @ rd @ 0b0011011
mapping clause encdec = PEXT_NARROWING_SHIFT_CLIP_H(rs2, rs1p, rd, PNCLIPU_HS) <->
  0b0 @ 0b010 @ 0b1 @ 0b01 @ rs2 @ rs1p @ 0b1100 @ rd @ 0b0011011
mapping clause encdec = PEXT_NARROWING_SHIFT_CLIP_H(rs2, rs1p, rd, PNCLIPRU_HS) <->
  0b0 @ 0b011 @ 0b1 @ 0b01 @ rs2 @ rs1p @ 0b1100 @ rd @ 0b0011011
mapping clause encdec = PEXT_NARROWING_SHIFT_CLIP_H(rs2, rs1p, rd, PNSRA_HS) <->
  0b0 @ 0b100 @ 0b1 @ 0b01 @ rs2 @ rs1p @ 0b1100 @ rd @ 0b0011011
mapping clause encdec = PEXT_NARROWING_SHIFT_CLIP_H(rs2, rs1p, rd, PNSRAR_HS) <->
  0b0 @ 0b101 @ 0b1 @ 0b01 @ rs2 @ rs1p @ 0b1100 @ rd @ 0b0011011
mapping clause encdec = PEXT_NARROWING_SHIFT_CLIP_H(rs2, rs1p, rd, PNCLIP_HS) <->
  0b0 @ 0b110 @ 0b1 @ 0b01 @ rs2 @ rs1p @ 0b1100 @ rd @ 0b0011011
mapping clause encdec = PEXT_NARROWING_SHIFT_CLIP_H(rs2, rs1p, rd, PNCLIPR_HS) <->
  0b0 @ 0b111 @ 0b1 @ 0b01 @ rs2 @ rs1p @ 0b1100 @ rd @ 0b0011011

function clause execute (PEXT_NARROWING_SHIFT_CLIP_H(rs2, rs1p, rd, op)) = {
  let rs1_val = X(rs1p @ 0b1) @ X(rs1p @ 0b0);
  let sa : bits(8) = EXTZ(X(rs2)[4..0]);
  var result : bits(32) = zeros();
  foreach (i from 0 to (32 - 16) by 16) {
    result[(i+15)..i] = match op {
      PNSRL_HS => shift_right_logic(rs1_val[(2*i+31)..(2*i)], sa)[15..0],
      PNCLIPU_HS => nclipu(rs1_val[(2*i+31)..(2*i)], sa)[15..0],
      PNCLIPRU_HS => nclipru(rs1_val[(2*i+31)..(2*i)], sa)[15..0],
      PNSRA_HS => shift_right_arith(rs1_val[(2*i+31)..(2*i)], sa)[15..0],
      PNSRAR_HS => shift_right_arith_rounding(rs1_val[(2*i+31)..(2*i)], sa)[15..0],
      PNCLIP_HS => nclips(rs1_val[(2*i+31)..(2*i)], sa)[15..0],
      PNCLIPR_HS => ncliprs(rs1_val[(2*i+31)..(2*i)], sa)[15..0]
    };
  };
  X(rd) = result;
  RETIRE_SUCCESS
}

mapping p_narrowing_shift_clip_h_mapping : p_narrowing_shift_clip_h <-> string = {
  PNSRL_HS <-> "pnsrl.hs",
  PNCLIPU_HS <-> "pnclipu.hs",
  PNCLIPRU_HS <-> "pnclipru.hs",
  PNSRA_HS <-> "pnsra.hs",
  PNSRAR_HS <-> "pnsrar.hs",
  PNCLIP_HS <-> "pnclip.hs",
  PNCLIPR_HS <-> "pnclipr.hs"
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
