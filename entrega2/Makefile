# Unix makefile for tigermain example

### LabBasica

#HOME=/home/alumno
#MOSMLHOME=${HOME}/mosml
#MOSMLTOOLS=${MOSMLHOME}/bin/camlrunm $(MOSMLHOME)/tools

### Casa

HOME=/home/alumno
MOSMLHOME=${HOME}/mosml
MOSMLTOOLS=camlrunm $(MOSMLHOME)/tools

MOSMLLEX=mosmllex
MOSMLYACC=mosmlyac -v

GCC=gcc
CFLAGS= -g
MOSMLC=mosmlc -c -liberal
MOSMLL=mosmlc

# Unix
REMOVE=rm -f
MOVE=mv
EXEFILE=

# DOS
#REMOVE=del
#MOVE=move
#EXEFILE=.exe

.SUFFIXES :
.SUFFIXES : .sig .sml .ui .uo

GRALOBJS= tigerabs.uo tigergrm.uo tigerlex.uo tigermain.uo \
	tigernlin.uo tigerpp.uo tigerescap.uo tigertab.uo tigerseman.uo tigertemp.uo topsort.uo tigertree.uo \
 	tigerframe.uo tigertrans.uo tigerit.uo tigerpila.uo tigerinterp.uo tigercanon.uo

all: tiger

tiger: $(GRALOBJS) $(OBJSGEN)
	$(MOSMLL) -o tiger $(EXEFILE) tigermain.uo

tigergrm.sml tigergrm.sig: tigergrm.y 
	$(MOSMLYACC) tigergrm.y

tigerlex.sml: tigerlex.lex
	$(MOSMLLEX) tigerlex.lex

clean:
	$(REMOVE) Makefile.bak
	$(REMOVE) tigergrm.output
	$(REMOVE) tigergrm.sig
	$(REMOVE) tigergrm.sml
	$(REMOVE) tigerlex.sml
	$(REMOVE) tiger
	$(REMOVE) *.ui
	$(REMOVE) *.uo
	$(REMOVE) errlist
	$(REMOVE) *.o

.sig.ui:
	$(MOSMLC) $<

.sml.uo:
	$(MOSMLC) $<

depend: tigerabs.sml tigergrm.sml tigerlex.sml tigermain.sml \
	tigernlin.sml tigerpp.sml topsort.sml
	$(REMOVE) Makefile.bak
	$(MOVE) Makefile Makefile.bak
	$(MOSMLTOOLS)/cutdeps < Makefile.bak > Makefile
	$(MOSMLTOOLS)/mosmldep >> Makefile

### DO NOT DELETE THIS LINE
tigerframe.uo: tigerframe.ui tigertree.uo tigertemp.ui 
tigerseman.uo: tigerseman.ui tigersres.uo tigertab.ui tigerpila.ui \
    topsort.ui tigerframe.ui tigertemp.ui tigerabs.uo tigertrans.ui 
tigersres.uo: tigertab.ui tigertips.uo tigertemp.ui tigerabs.uo \
    tigertrans.ui 
tigercanon.ui: tigertree.uo tigertemp.ui 
tigertemp.uo: tigertemp.ui 
topsort.uo: topsort.ui tigersres.uo 
tigerescap.uo: tigerescap.ui tigertab.ui tigerabs.uo 
tigerseman.ui: tigertab.ui tigertips.uo tigerabs.uo 
tigergrm.ui: tigerabs.uo 
tigertab.uo: tigertab.ui 
tigerinterp.uo: tigerinterp.ui tigertree.uo tigertab.ui tigerframe.ui \
    tigerit.uo tigertemp.ui 
tigerpp.uo: tigerabs.uo 
tigerframe.ui: tigertree.uo tigertemp.ui 
topsort.ui: tigerseman.ui tigerabs.uo 
tigercanon.uo: tigercanon.ui tigertree.uo tigertab.ui tigertemp.ui 
tigertrans.ui: tigertree.uo tigerframe.ui tigertemp.ui tigerabs.uo 
tigerpila.uo: tigerpila.ui 
tigertree.uo: tigertemp.ui 
tigerinterp.ui: tigertree.uo tigerframe.ui tigertemp.ui 
tigermain.uo: tigerseman.ui tigerescap.ui tigergrm.ui tigerframe.ui \
    tigercanon.ui tigerinterp.ui tigerlex.uo tigertrans.ui tigerpp.uo 
tigerit.uo: tigertree.uo tigertab.ui 
tigerescap.ui: tigerabs.uo 
tigergrm.uo: tigergrm.ui tigernlin.uo tigerabs.uo 
tigertrans.uo: tigertrans.ui tigertree.uo tigerpila.ui tigerframe.ui \
    tigerit.uo tigertemp.ui tigerabs.uo 
tigerlex.uo: tigergrm.ui tigernlin.uo 
