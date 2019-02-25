package breu

case class Goal(val subGoals : Seq[Seq[(Int, Int)]]) {
  override def toString = subGoals.mkString(" OR ")

  def stringWithTermMap(intMap : Map[Int, String]) = {
    subGoals.map(sg => sg.map{ case (s,t) => (intMap(s), intMap(t)) }).mkString(" OR ")
  }

  val terms : Set[Int] = subGoals.flatten.map(x => List(x._1, x._2)).flatten.toSet
  def contains(term : Int) : Boolean = {
    for (g <- subGoals)
      for ((s, t) <- g)
        if (s == term || t == term)
          return true
    return false
  }

}

case class Eq(val fun : Int, val args : Seq[Int], val res : Int) {
  override def toString = fun + "(" + args.mkString(",") + ")=" + res

  def stringWithTermMap(intMap : Map[Int, String]) = {
    fun + "(" + args.map(intMap(_)).mkString(",") + ")=" + intMap(res)
  }
  val terms : Set[Int] = args.toSet + res
  def contains(term : Int) : Boolean = {
    if (res == term)
      return true
    for (a <- args)
      if (a == term)
        return true
    return false
  }
}

case class Domains(val domains : Map[Int, Set[Int]]) {
  override def toString = domains.mkString("\n")
  def apply(i : Int) = {
    domains.getOrElse(i, Set(i))
  }

  val terms : Set[Int]  = (for ((_, d) <- domains) yield d).flatten.toSet
}

case class SubProblem(
  val terms : Seq[Int],
  // val domains : Domains,
  val funEqs : Seq[Eq],
  val goal : Goal,
  val DQ : Disequalities,
  val baseDQ : Disequalities) {

  override def toString = {
    "+---SP----\n" +
    "| funEqs: " + funEqs.mkString("\n") + "\n" +
    "| goal: " + goal + "\n" +
    "+---------\n"
  }


  def toTermString(termMap : Map[Int, String]) = {
    "+---SP----\n" +
    "| funEqs: " + funEqs.map(_.stringWithTermMap(termMap)) + "\n" +
    "| goal: " + goal.stringWithTermMap(termMap) + "\n" +
    "+---------\n"    
  }


  def solvable = {
    // subgoalsat(0) = true of subgoal(0) is solvable
    val subgoalsat = for (subgoal <- goal.subGoals) yield
      (for ((s, t) <- subgoal) yield DQ(s, t)).foldRight(true)(_ && _)

    subgoalsat.foldRight(false)(_ || _)
  }

  def verifySolution(solution : Map[Int, Int]) = {
    val uf = Util.BreunionFind(terms, funEqs, solution.toList)
    var satisfiable = false

    for (subGoal <- goal.subGoals) {
      var subGoalSat = true

      var allPairsTrue = true
      for ((s,t) <- subGoal) {
        if (uf(s) != uf(t)) {
          allPairsTrue = false
        }

        if (!allPairsTrue)
          subGoalSat = false
      }
      if (subGoalSat) {
        satisfiable = true
      }
    }
    satisfiable    
  }
}
