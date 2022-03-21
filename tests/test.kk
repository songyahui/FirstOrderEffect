effect yield
  ctl yield() : ()


fun code() {
  var i := 0
  yield();
  i := i + 1
  println(i) // println output
}

fun main () {
  with ctl yield()
    println("yielded ")
    resume(())
    resume(())
  code()
}