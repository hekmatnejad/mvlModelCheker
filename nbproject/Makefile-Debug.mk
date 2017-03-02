#
# Generated Makefile - do not edit!
#
# Edit the Makefile in the project folder instead (../Makefile). Each target
# has a -pre and a -post target defined where you can add customized code.
#
# This makefile implements configuration specific macros and targets.


# Environment
MKDIR=mkdir
CP=cp
GREP=grep
NM=nm
CCADMIN=CCadmin
RANLIB=ranlib
CC=gcc
CCC=g++
CXX=g++
FC=gfortran
AS=as

# Macros
CND_PLATFORM=GNU-Linux
CND_DLIB_EXT=so
CND_CONF=Debug
CND_DISTDIR=dist
CND_BUILDDIR=build

# Include project Makefile
include Makefile

# Object Directory
OBJECTDIR=${CND_BUILDDIR}/${CND_CONF}/${CND_PLATFORM}

# Object Files
OBJECTFILES= \
	${OBJECTDIR}/MvLtlModel.o \
	${OBJECTDIR}/TestMain.o \
	${OBJECTDIR}/TestSuite.o \
	${OBJECTDIR}/Util.o \
	${OBJECTDIR}/main.o


# C Compiler Flags
CFLAGS=-lspot -lbddx

# CC Compiler Flags
CCFLAGS=-lspot -lbddx
CXXFLAGS=-lspot -lbddx

# Fortran Compiler Flags
FFLAGS=

# Assembler Flags
ASFLAGS=

# Link Libraries and Options
LDLIBSOPTIONS=`pkg-config --libs cpputest`  

# Build Targets
.build-conf: ${BUILD_SUBPROJECTS}
	"${MAKE}"  -f nbproject/Makefile-${CND_CONF}.mk ${CND_DISTDIR}/${CND_CONF}/${CND_PLATFORM}/mvltlproject

${CND_DISTDIR}/${CND_CONF}/${CND_PLATFORM}/mvltlproject: ${OBJECTFILES}
	${MKDIR} -p ${CND_DISTDIR}/${CND_CONF}/${CND_PLATFORM}
	g++ -o ${CND_DISTDIR}/${CND_CONF}/${CND_PLATFORM}/mvltlproject ${OBJECTFILES} ${LDLIBSOPTIONS} -lspot -lbddx -lspotltsmin

${OBJECTDIR}/MvLtlModel.o: MvLtlModel.cpp
	${MKDIR} -p ${OBJECTDIR}
	${RM} "$@.d"
	$(COMPILE.cc) -g `pkg-config --cflags cpputest` -std=c++11  -MMD -MP -MF "$@.d" -o ${OBJECTDIR}/MvLtlModel.o MvLtlModel.cpp

${OBJECTDIR}/TestMain.o: TestMain.cpp
	${MKDIR} -p ${OBJECTDIR}
	${RM} "$@.d"
	$(COMPILE.cc) -g `pkg-config --cflags cpputest` -std=c++11  -MMD -MP -MF "$@.d" -o ${OBJECTDIR}/TestMain.o TestMain.cpp

${OBJECTDIR}/TestSuite.o: TestSuite.cpp
	${MKDIR} -p ${OBJECTDIR}
	${RM} "$@.d"
	$(COMPILE.cc) -g `pkg-config --cflags cpputest` -std=c++11  -MMD -MP -MF "$@.d" -o ${OBJECTDIR}/TestSuite.o TestSuite.cpp

${OBJECTDIR}/Util.o: Util.cpp
	${MKDIR} -p ${OBJECTDIR}
	${RM} "$@.d"
	$(COMPILE.cc) -g `pkg-config --cflags cpputest` -std=c++11  -MMD -MP -MF "$@.d" -o ${OBJECTDIR}/Util.o Util.cpp

${OBJECTDIR}/main.o: main.cpp
	${MKDIR} -p ${OBJECTDIR}
	${RM} "$@.d"
	$(COMPILE.cc) -g `pkg-config --cflags cpputest` -std=c++11  -MMD -MP -MF "$@.d" -o ${OBJECTDIR}/main.o main.cpp

# Subprojects
.build-subprojects:

# Clean Targets
.clean-conf: ${CLEAN_SUBPROJECTS}
	${RM} -r ${CND_BUILDDIR}/${CND_CONF}

# Subprojects
.clean-subprojects:

# Enable dependency checking
.dep.inc: .depcheck-impl

include .dep.inc
