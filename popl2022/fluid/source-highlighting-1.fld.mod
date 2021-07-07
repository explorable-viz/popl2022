let map f [] = [];
    map f (x : xs) = f x : map f xs;
let data = [
   { energyType: "Bio", output: 6.2 },
   { energyType: (*@\codeSel{"Hydro"}@*), output: 260 },
   { energyType: "Solar", output: 19.9 },
   { energyType: "Wind", output: 91 },
   { energyType: (*@\codeSelTwo{"Geo"}@*), output: 14.4 }
];
let xs = (*@\codeSel{[}@*) row.output
   | type $\leftarrow$ [(*@\codeSel{"Hydro"}@*), "Solar", (*@\codeSelTwo{"Geo"}@*)],
     row $\leftarrow$ data, row.energyType == type
(*@\codeSel{]}@*) in
map (fun x $\rightarrow$ floor (x / sum xs * 100)) xs
$\Rightarrow$ (88 (*@\codeSel{:}@*) (6 : (4 (*@\codeSelTwo{:}@*) [])))