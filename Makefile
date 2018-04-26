all:
	scalac -classpath "lib/org.sat4j.core.jar" \
	-d bin/breu.jar \
	src/breu/BenchSolver.scala \
	src/breu/LazySolver.scala \
	src/breu/Timeout.scala \
	src/breu/BREUProblem.scala \
	src/breu/BREUSolver.scala \
	src/breu/Timer.scala \
	src/breu/BREUInstance.scala \
	src/breu/Goal.scala \
	src/breu/TableSolver.scala \
	src/breu/Util.scala \
	src/breu/api.scala \
	src/breu/BREUConstructor.scala

