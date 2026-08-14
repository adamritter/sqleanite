set here [file dirname [file normalize [info script]]]
if {[llength $argv] != 1} {error "usage: tclsh runner.tcl TEST-NAME"}
set argv0 [file join $here runner.tcl]
source [file join $here .. "[lindex $argv 0].test"]

