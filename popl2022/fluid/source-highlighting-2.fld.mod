let map f [] = [];
    map f (x : xs) = f x : map f xs;
let data = [
   { energyType: "Bio", output: 6.2 },
   { energyType: "Hydro", output: (*@\codeErase{260}@*) },
   { energyType: "Solar", output: (*@\codeErase{19.9}@*) },
   { energyType: "Wind", output: 91 },
   { energyType: (*@\codeSel{"Geo"}@*), output: (*@\codeErase{14.4}@*) }
];
let xs = (*@\codeSel{[}@*) row.output
   | type $\leftarrow$ ["Hydro", "Solar", (*@\codeSel{"Geo"}@*)],
     row $\leftarrow$ data, row.energyType == type
(*@\codeSel{]}@*) in
map (fun x $\rightarrow$ floor (x / sum xs * (*@\codeErase{100}@*))) xs
$\Rightarrow$ (88 : ((*@\codeErase{6}@*) : (4 (*@\codeSelTwo{:}@*) [])))