# autoprover
Usage: `./autoprover.py theorem/<theorem_name>.v -b tactic_set/<tactics_name>`

Use `./autoprover.py -h` for further information.

## Dependence
* Coq: 8.5pl3 (December 2016)
* python: 3.6.0

## Command
1. `show-proof`: display all found proofs.
2. `next <step>` or `n <step>`: evolove for `<step>` generations.
3. `edit <n>` or `e <n>`: edit the n-th gene.
4. `list <n> [property]` or `l <n> [property]`: display the n-th gene's property, default is fitness and running states of coq.
5. `set pop <property> <n> <value>`: set proptery for a individual of population.
6. `stats`: display tactics usage.
7. `save <filename>`: save a snatshop of population.
8. `load <filename>`: load a snameshop from file.
9. `read <filename>`: read a rule from file.
10. `del <n>`: remove the n-th rules from rules set.
11. `rm`: remove a tactic from the population.
  
## Example: the divisibility rule for 3

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
