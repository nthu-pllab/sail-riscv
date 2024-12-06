union clause ast = PEXT_SIMPLE : (regidx, regidx, psimple)

mapping clause encdec = PEXT_SIMPLE(rs1, rd, CLS) <->
  0b01100 @ 0b0000011 @ rs1 @ 0b001 @ rd @ 0b0010011
mapping clause encdec = PEXT_SIMPLE(rs1, rd, CLSW) if sizeof(xlen) == 64 <->
  0b01100 @ 0b0000011 @ rs1 @ 0b001 @ rd @ 0b0011011 if sizeof(xlen) == 64
mapping clause encdec = PEXT_SIMPLE(rs1, rd, ABS) <->
  0b01100 @ 0b0000111 @ rs1 @ 0b001 @ rd @ 0b0010011
mapping clause encdec = PEXT_SIMPLE(rs1, rd, ABSW) if sizeof(xlen) == 64 <->
  0b01100 @ 0b0000111 @ rs1 @ 0b001 @ rd @ 0b0011011 if sizeof(xlen) == 64
mapping clause encdec = PEXT_SIMPLE(rs1, rd, REV) if sizeof(xlen) == 32 <->
  0b01101 @ 0b0011111 @ rs1 @ 0b101 @ rd @ 0b0010011 if sizeof(xlen) == 32
mapping clause encdec = PEXT_SIMPLE(rs1, rd, REV) if sizeof(xlen) == 64 <->
  0b01101 @ 0b0111111 @ rs1 @ 0b101 @ rd @ 0b0010011 if sizeof(xlen) == 64
mapping clause encdec = PEXT_SIMPLE(rs1, rd, REV8) if sizeof(xlen) == 32 <->
  0b01101 @ 0b0011000 @ rs1 @ 0b101 @ rd @ 0b0010011 if sizeof(xlen) == 32
mapping clause encdec = PEXT_SIMPLE(rs1, rd, REV8) if sizeof(xlen) == 64 <->
  0b01101 @ 0b0111000 @ rs1 @ 0b101 @ rd @ 0b0010011 if sizeof(xlen) == 64
mapping clause encdec = PEXT_SIMPLE(rs1, rd, REV16) if sizeof(xlen) == 64 <->
  0b01101 @ 0b0110000 @ rs1 @ 0b101 @ rd @ 0b0010011 if sizeof(xlen) == 64

function clause execute (PEXT_SIMPLE(rs1, rd, op)) = {
  match op {
    CLS => {
      let rs1_val = X(rs1);
      var result : nat = 0;
      var done : bool = false;
      foreach (i from (sizeof(xlen) - 2) downto 0)
        if not(done) then if rs1_val[i] == rs1_val[sizeof(xlen) - 1]
                        then result = result + 1
                        else done = true;
      X(rd) = to_bits(sizeof(xlen), result);
    },
    CLSW => {
      let rs1_val = X(rs1);
      var result : nat = 0;
      var done : bool = false;
      foreach (i from 30 downto 0)
        if not(done) then if rs1_val[i] == rs1_val[31]
                        then result = result + 1
                        else done = true;
      X(rd) = to_bits(sizeof(xlen), result);
    },
    ABS => if X(rs1) <_s zeros() then X(rd) = not_vec(X(rs1)) + 1 else X(rd) = X(rs1),
    ABSW => { // TODO: Double check if this is correct.
      let rs1_val = X(rs1);
      let rs1_word = slice(rs1_val, 0, 32);
      let result : xlenbits = if rs1_word <_s zeros() then EXTZ (not_vec(rs1_word) + 1) else EXTZ(rs1_word);
      X(rd) = result;
    },
    REV => {
      let rs1_val = X(rs1);
      var result : xlenbits = zeros();
      foreach (i from 0 to (sizeof(xlen) - 1))
        result[i] = rs1_val[(sizeof(xlen) - i - 1)];
      X(rd) = result;
    },
    REV8 => {
      let rs1_val = X(rs1);
      var result : xlenbits = zeros();
      foreach (i from 0 to (sizeof(xlen) - 8) by 8)
        result[(i + 7) .. i] = rs1_val[(sizeof(xlen) - i - 1) .. (sizeof(xlen) - i - 8)];
      X(rd) = result;
    },
    REV16 => {
      let rs1_val = X(rs1);
      var result : xlenbits = zeros();
      foreach (i from 0 to (sizeof(xlen) - 16) by 16)
        result[(i + 15) .. i] = rs1_val[(sizeof(xlen) - i - 1) .. (sizeof(xlen) - i - 16)];
      X(rd) = result;
    }
  };
  RETIRE_SUCCESS
}

mapping p_simple_mapping : psimple <-> string = {
  CLS <-> "cls",
  CLSW <-> "clsw",
  ABS <-> "abs",
  ABSW <-> "absw",
  REV <-> "rev",
  REV8 <-> "rev8",
  REV16 <-> "rev16"
}

mapping clause assembly = PEXT_SIMPLE(rs1, rd, p_inst)
  <-> p_simple_mapping(p_inst) ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1)