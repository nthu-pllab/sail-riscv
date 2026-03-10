// =======================================================================================
// This Sail RISC-V architecture model, comprising all files and
// directories except where otherwise noted is subject the BSD
// two-clause license in the LICENSE file.
//
// SPDX-License-Identifier: BSD-2-Clause
// =======================================================================================

// ******************************************************************************
// This file implements part of the pack extension.
// ******************************************************************************

// ****************************** P MISC ****************************************
union clause instruction = PMISC : (pmiscfunct7, regidx, regidx)

mapping encdec_pmiscfunct7 : pmiscfunct7 <-> bits(7) = {
    CLS <-> 0b0000011,
    ABS <-> 0b0000111,
}

mapping clause encdec = PMISC(funct7, rs1, rd)
  <-> 0b01100 @ encdec_pmiscfunct7(funct7) @ encdec_reg(rs1) @ 0b001 @ encdec_reg(rd) @ 0b0010011

function clause execute (PMISC(funct7, rs1, rd)) = {
  match funct7 {
    CLS => X(rd) = to_bits(count_leading_sign_bits(X(rs1))),
    ABS => X(rd) = abs(X(rs1)),
  };
  RETIRE_SUCCESS
}

mapping pmisc_mnemonic : pmiscfunct7 <-> string = {
  CLS <-> "cls",
  ABS <-> "abs",
}

mapping clause assembly = PMISC(funct7, rs1, rd)
  <-> pmisc_mnemonic(funct7) ^ spc() ^ reg_name(rd) ^ sep() ^ sep() ^ reg_name(rs1)

// ****************************** P REV, REV16 ****************************************
union clause instruction = PREV : (regidx, regidx)

mapping clause encdec = PREV(rs1, rd)
  <-> 0b01101 @ 0b0111111 @ encdec_reg(rs1) @ 0b001 @ encdec_reg(rd) @ 0b0010011

function clause execute (PREV(rs1, rd)) = {
  let rs1_val = X(rs1);
  var result : xlenbits = zeros();
  foreach (i from 0 to (sizeof(xlen) - 1))
    result[i] = rs1_val[(sizeof(xlen) - i - 1)];
  X(rd) = result;
  RETIRE_SUCCESS
}

mapping clause assembly = PREV(rs1, rd)
  <-> "rev" ^ spc() ^ reg_name(rd) ^ sep() ^ sep() ^ reg_name(rs1)
