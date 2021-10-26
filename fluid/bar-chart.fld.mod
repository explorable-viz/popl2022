let totalFor c rows =
   sum [ row.output | row $\leftarrow$ rows, row.country == c ];
let data2015 = [ row | row $\leftarrow$ data, row.year == 2015 ];
    countryData = [ { x: c, y: totalFor c data2015 }
                  | c $\leftarrow$ ["China", "USA", "Germany"] ]
in BarChart { caption: "Total output by country", data: countryData }
