***************************************************************
*                   Screamer Tool Repository                  *
*                     (ftp.cis.upenn.edu)                     *
*                                                             *
*                 [Last updated: June 1, 1994]                *
***************************************************************

This directory contains the Screamer distribution and user-contributed
code based on Screamer.  At the end of this note, you will find the
FAQ file distributed with Screamer which briefly describes what
Screamer is and on which platforms it currently runs.  The repository
is available via ftp at ftp.cis.upenn.edu, or the WWW (for retrieval
only) at "http://www.cis.upenn.edu/~screamer-tools/home.html".

The organization of the repository is as follows:

ftp.cis.upenn.edu:
   /pub/screamer.tar.Z             Screamer distribution
   /pub/screamer-tools/
                       incoming/   for people to drop code off
                       contrib/    user-contributed code
                       INDEX       A file that indexes contributions
                       README      Introduction to site (this file)

If you retrieve the Screamer distribution from us, please be advised
that you must still follow the instructions given in the README file
of the distribution.  You are free to use, copy, and distribute
Screamer according to the policies described in that file (essentially
that you notify the maintainers of Screamer of any bugs, bug fixes,
and your obtaining a copy).

Because this machine is heavily used during the day by staff,
researchers, and students at the University of Pennsylvania, please
try to refrain from FTPing files between 9am and 5pm EST (GMT -0500).

All contributions should be placed in the pub/screamer-tools/incoming
subdirectory.  If you contribute code, please write me a note (at
screamer-repository@cis.upenn.edu) stating the filename(s) of your
contribution and a brief description.  Where applicable, this
description should include which platform(s) the code has been tested.
I will place this description in the file in pub/screamer-tools/INDEX.

Alternatively, you may mail me the contribution directly, at

	screamer-repository@cis.upenn.edu

The preferred format for files is as a uuencoded compressed tar file,
but other formats are okay.  If they get too exotic (i.e., I can't
unpack them), I will let you know.  For consistency, I may repackage
the contribution.


- Jonathan Kaye
  Librarian and all-around-good-guy
  (kaye@linc.cis.upenn.edu)

We want to acknowledge the assistance of Mark Foster and Mark-Jason
Dominus for arranging the administrative tasks involved in setting up
this repository.

**********************************************************************

NO WARRANTY 

Because this repository is a free service, we provide absolutely no
warranty on Screamer or the user-contributed software.  All software
is provided "as is" from the respective authors.

In no event, unless required by applicable law will the Massachusetts
Institute of Technology, the University of Pennsylvania, the
University of Toronto, Jeffrey Mark Siskind, David Allen McAllester,
and/or the Repository Librarian be liable to you for damages,
including any lost profits, lost monies, or other special, incidental,
or consequential damages arising out of the use or inability to use
the software.

**********************************************************************
Screamer is an extension of Common Lisp that adds support for nondeterministic
programming.  Screamer consists of two levels.  The basic nondeterministic
level adds support for backtracking and undoable side effects.  On top of this
nondeterministic substrate, Screamer provides a comprehensive constraint
programming language in which one can formulate and solve mixed systems of
numeric and symbolic constraints.  Together, these two levels augment Common
Lisp with practically all of the functionality of both Prolog and constraint
logic programming languages such as CHiP and CLP(R).  Furthermore, Screamer is
fully integrated with Common Lisp. Screamer programs can coexist and
interoperate with other extensions to Common Lisp such as CLOS, CLIM and
Iterate.

In several ways Screamer is more efficient than other implementations of
backtracking languages.  First, Screamer code is transformed into Common Lisp
which can be compiled by the underlying Common Lisp system.  Many competing
implementations of nondeterministic Lisp are interpreters and thus are far
less efficient than Screamer.  Second, the backtracking primitives require
fairly low overhead in Screamer.  Finally, this overhead to support
backtracking is only paid for those portions of the program which use the
backtracking primitives.  Deterministic portions of user programs pass through
the Screamer-to-Common-Lisp transformation unchanged.  Since in practise, only
small portions of typical programs utilize the backtracking primitives,
Screamer can produce more efficient code than compilers for languages in which
backtracking is more pervasive.

Screamer is fairly portable across most Common Lisp implementations. Screamer
is known to run under the following Common Lisp implementations:

   Genera 8.1.1 and 8.3 on Symbolics 36xx and Ivory.
   Lucid 4.0.2 and 4.1 on Sun SPARC.
   Lucid 4.1 on SGI MIPS.
   Lucid 4.1 on HP PA.
   Lucid 4.1 on DEC MIPS.
   Lucid 4.0.1 on IBM RS/6000.
   MCL 2.0 and 2.0p2 on Apple Macintosh.
   Harlequin 3.0.3+ on Sun SPARC.
   Allegro 4.1 and 4.2 on Sun SPARC and SGI MIPS.
   Allegro 4.1 on DEC MIPS.
   Poplog 14.2 on Sun SPARC.
   AKCL 1.605 and 1.615 on Sun SPARC.
   CMU Common Lisp 17b on Sun SPARC.

It should run under any implementation of Common Lisp that is compliant with
CLtL2 and with minor revision could be made to run under implementations
compliant with CLtL1 or dpANS.

Screamer was written by Jeffrey Mark Siskind and David Allen McAllester.
It is available by anonymous FTP from either ftp.ai.mit.edu,
ftp.cis.upenn.edu, or ftp.cs.toronto.edu as the file /pub/qobi/screamer.tar.Z.
Contact Jeffrey Mark Siskind (Qobi@CS.Toronto.EDU) for further information.
