let series type country = [
   { x: year, y: row.output }
   | year $\leftarrow$ [2013..2018], row $\leftarrow$ data,
     row.year == year, row.energyType == type, row.country == country
] in LineChart {
   caption: "Output of USA relative to China",
   plots: [
      LinePlot { name: type, data: plot }
      | type $\leftarrow$ ["Bio", "Hydro", "Solar", "Wind"],
        let plot = zipWith (fun p1 p2 $\rightarrow$ { x: p1.x, y: p1.y / p2.y })
                           (series type "USA") (series type "China")
   ]
}
