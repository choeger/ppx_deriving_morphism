Changelog
=========

0.3
---	
	* Fix name-clash in case of "type t":
	Names are now map_routines/fold_routines for the generated
	records.
	* Rename on_<t> to dispatch_<t>
	This is simply more readable (routine "on" does not carry much
	information in the case of "type t")
	
0.1
---
* Initial alpha-release to test the concept
