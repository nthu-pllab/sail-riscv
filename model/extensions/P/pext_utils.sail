val count_leading_sign_bits : forall 'n, 'n == 32 | 'n == 64. (bits('n)) -> range(0, 'n)
function count_leading_sign_bits(x) = {
  var count : range(0, 'n) = 0;
  var continue : bool = true;
  let msb : bit = x['n - 1];

  foreach (i from ('n - 1) downto 0) {
    if x[i] == msb & continue then {
      let new_count = count + 1;
      assert(new_count <= 'n);
      count = new_count;
    } else {
      continue = false;
    }
  };
  count
}

val abs : forall 'n, 'n == 32 | 'n == 64. (bits('n)) -> (bits('n))
function abs(x) = {
  var res : bits('n) = x;

  if res['n - 1] == bitone then {
    res = ~(res) + zero_extend(0b1);
  };

  res
}