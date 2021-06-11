let edgeDetect = [[0,  1, 0],
                  [1, -4, 1],
                  [0,  1, 0]];
    filter = $\langle$ nth2 i j edgeDetect | (i, j) in (3, 3) $\rangle$;
    image' = [[15, 13,  6, 9, 16],
              [12,  5, 15, 4, 13],
              [14,  9, 20, 8,  1],
              [ 4, 10,  3, 7, 19],
              [ 3, 11, 15, 2,  9]];
    image = $\langle$ nth2 i j image' | (i, j) in (5, 5) $\rangle$
in convolve image filter extend
