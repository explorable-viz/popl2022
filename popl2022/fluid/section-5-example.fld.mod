let map f [] = [];
    map f (x : xs) = f x : map f xs;
let data = [
   { year: 2013, country: "China", energyType: "Bio", output: 6.2 },
   { year: 2013, country: "China", energyType: "Hydro", output: 260 },
   { year: 2013, country: "China", energyType: "Solar", output: 19.9 },
   { year: 2013, country: "China", energyType: "Wind", output: 91 }
];
   output = [
   row.output | type $\leftarrow$ ["Bio", "Hydro", "Solar", "Wind"],
                row $\leftarrow$ data, row.energyType == type
] in
map (fun x $\rightarrow$ floor (x / sum output * 100)) output
