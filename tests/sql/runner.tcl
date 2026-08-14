set here [file dirname [file normalize [info script]]]
if {[llength $argv] != 2} {
  error "usage: tclsh runner.tcl SQLITE-TEST-DIR TEST-NAME"
}
set upstream [file normalize [lindex $argv 0]]
set testname [lindex $argv 1]
set argv0 [file join $here runner.tcl]
source [file join $upstream "$testname.test"]
