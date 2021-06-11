let china =
   [ row | row $\leftarrow$ data, row.country == "China" ];
let series type rows = [
   {x: year, y: row.output }
   | year $\leftarrow$ [2013..2018], row $\leftarrow$ rows,
     row.year == year, row.energyType == type
] in LineChart {
   caption: "Growth in renewables for China",
   plots: [
      LinePlot { name: type, data: series type china }
      | type $\leftarrow$ ["Bio", "Hydro", "Solar", "Wind"]
   ]
}
