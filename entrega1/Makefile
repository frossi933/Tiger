# Unix makefile for tigermain example

#HOME=/home/alumno
#MOSMLHOME=${HOME}/mosml
#MOSMLTOOLS=${MOSMLHOME}/bin/camlrunm $(MOSMLHOME)/tools

#MOSMLLEX=${MOSMLHOME}/bin/mosmllex
#MOSMLYACC=${MOSMLHOME}/bin/mosmlyac -v


MOSMLLEX=mosmllex
MOSMLYACC=mosmlyac

GCC=gcc
CFLAGS= -g

#MOSMLC=${MOSMLHOME}/bin/mosmlc -c -liberal
#MOSMLL=${MOSMLHOME}/bin/mosmlc

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
	tigernlin.uo tigerpp.uo tigerescap.uo tigertab.uo tigerseman.uo tigertemp.uo topsort.uo

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
	$(REMOVE) tigermain
	$(REMOVE) *.ui
	$(REMOVE) *.uo
	$(REMOVE) errlist
	$(REMOVE) *.o

.sig.ui:
	$(MOSMLC) $<

.sml.uo:
	$(MOSMLC) $<

depend: tigerabs.sml tigergrm.sml tigerlex.sml tigermain.sml \
	tigernlin.sml tigerpp.sml
	$(REMOVE) Makefile.bak
	$(MOVE) Makefile Makefile.bak
	$(MOSMLTOOLS)/cutdeps < Makefile.bak > Makefile
	$(MOSMLTOOLS)/mosmldep >> Makefile

### DO NOT DELETE THIS LINE
topsort.uo: topsort.ui tigersres.uo 
tigerpp.uo: tigerabs.uo 
tigertemp.uo: tigertemp.ui 
tigertab.uo: tigertab.ui 
tigersres.uo: tigertab.ui tigertips.uo tigertemp.ui tigerabs.uo 
tigerlex.uo: tigergrm.ui tigernlin.uo 
tigerseman.uo: tigerseman.ui tigersres.uo tigertab.ui topsort.ui \
    tigertemp.ui tigerabs.uo 
tigerescap.ui: tigerabs.uo 
tigergrm.ui: tigerabs.uo 
tigergrm.uo: tigergrm.ui tigernlin.uo tigerabs.uo 
tigerescap.uo: tigerescap.ui tigertab.ui tigerabs.uo 
tigermain.uo: tigerseman.ui tigerescap.ui tigergrm.ui tigerlex.uo \
    tigerpp.uo 
topsort.ui: tigerseman.ui tigerabs.uo 
tigerseman.ui: tigertab.ui tigertips.uo tigerabs.uo 
