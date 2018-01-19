const { readFileSync } = require('fs')
const parse = require('csv-parse/lib/sync')
const { range, flatMap, includes, findIndex, pull, chain } = require('lodash')

const namesFile = readFileSync('names.csv').toString()
const names = parse(namesFile)[0]

const pre = 'solution'
const post = '.csv'
for (const n of range(1, 2.1)) {
  const solutionFile = readFileSync(pre + n + post).toString()
  const solution = parse(solutionFile).map(arr => arr.map(Number))
  const visited = flatMap(
    solution, (arr, i) => includes(arr, 1) ? [ i ] : []
  )

  const tours = [];
  while (visited.length) {
    const start = visited[0];
    const tour = [];
    let curr = start;
    do {
      pull(visited, curr)
      tour.push(curr)
      curr = findIndex(solution[curr], Boolean)
    } while (curr != start)
    tours.push(tour)
  }

  chain(tours)
    .groupBy('length')
    .forEach(tours => {
      tours
      .forEach(tour => {
        console.log(`  ,  (${tour.map(i => names[i]).join(', ')})`)
      })
    })
    .value()
  console.log()
}

function showNames(arr) {
  arr.forEach(v => console.log(names[v]))
}
