# autoprover
Example `./autoprover.py theorem/<theorem_name>.v -b tactic_set/<tactics_name>`

## Divisibility rule for 3

1. Run the proof generator.
`./autoprover.py theorem/div3.v -b tactic_set/div3.txt`

2. Read rules.

  * `div3 > read rules/r1.json`
  * `div3 > read rules/r2.json`
  * `div3 > read rules/r3.json`

3. Evolve population for generations.

  * `div3 > n 35`

4. Use `show-proof` to check if a proof is found.

  * `div3 > show-proof`

5. Repeat 3, 4.
