// Thanks to: https://gist.github.com/justinhj/e2eb081af1f8a341f957e2f8bc4e9686

package breu

import java.util.{Timer => ScalaTimer, TimerTask}
import scala.concurrent.{Future, Promise, ExecutionContext => EC, TimeoutException}

object Timeout {

  val timer: ScalaTimer = new ScalaTimer(true)

  def futureWithTimeout[T](future : Future[T], timeout : Long)(implicit ec: EC): Future[T] = {

    var result = Promise[T]

    val tt = new TimerTask() { def run() : Unit = { result.tryFailure(new TimeoutException()) } }

    timer.schedule(tt, timeout)

    future.map {
      a => if(result.trySuccess(a)) { tt.cancel() }
    }.recover {
      case e: Exception => if(result.tryFailure(e)) { tt.cancel() }
    }

    result.future
  }

}
