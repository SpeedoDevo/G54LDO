# INCLUDED EXTRA FILES

* `cw-lbd-4211949-manual.mod`:
  A formulation that uses manual subtour breaking. Faster, but less reliable.
* `package.json` & `process.js`:
  An extra script I developed to help verify solutions and break subtours.

  To use this you'll need [glpk](https://www.gnu.org/software/glpk/) to export
  solutions to CSV, and [Node.js](https://nodejs.org/) to run the script. After
  installing Node.js run `npm install` in the script directory, to fetch some
  dependencies.

  Make sure that both the solver and node is on your PATH, and that the CSV
  part of the model is active then you can run
  `glpsol.exe -m cw-lbd-4211949.mod && node process.js` to generate the solution
  and run the script that processes it.

  It will output something like this:
  ```
  ,  (Heathrow, Islington, Holborn, Battersea, Greenwich, Woolwich, Barking)

  ,  (Heathrow, Harrow, Ealing, Hammersmith, Richmond, Kingston, Sutton, Bromley, Dartford)
  ```

  All cycles by all vans in a format that can be copied to be added as subtour
  breaking constraint.
