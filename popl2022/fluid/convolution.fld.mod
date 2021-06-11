let zero n = const n;
    wrap n n_max = ((n - 1) `mod` n_max) + 1;
    extend n = min (max n 1);
    nth2 i j xss = nth (j - 1) (nth (i - 1) xss);

let convolve image filter method =
    let ((m, n), (i, j)) = (dims image, dims filter);
        (half_i, half_j) = (i `quot` 2, j `quot` 2);
        area = i * j
    in  $\langle$ (sum [ image!(x, y) * filter!(i' + 1, j' + 1)
                | (i', j') $\leftarrow$ range (0, 0) (i - 1, j - 1),
                  let x = method (m' + i' - half_i) m,
                  let y = method (n' + j' - half_j) n,
                  x $\numgeq$ 1, x $\numleq$ m, y $\numgeq$ 1, y $\numleq$ n ])
           `quot` area
         | (m', n') in (m, n) $\rangle$;
