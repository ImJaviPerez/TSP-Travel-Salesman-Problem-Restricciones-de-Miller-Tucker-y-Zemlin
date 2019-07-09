/*
TSP con las restricciones de Miller, Tucker y Zemlin

Nombre: tsp.mtz.mod
Autor: F. Javier Perez Ramirez
Fecha: 12-01-2018
version: 1.0
software: Gusek. http://gusek.sourceforge.net/gusek.html

Descripcion:
Problema del Viajante de Comercio
(TSP): Consideremos un grafo no orientado G=(N,E) con costo c_e asociado a cada arista e \in E.
El Problema del Viajante de Comercio consiste en determinar un ciclo (cerrado) en G 
en el que se recorren todos los nodos del grafo una sola vez y 
cuyas aristas tengan un costo total m�nimo.
Se suele asumir que el grafo G es completo, o sea, que existen todas las aristas posibles.

- N es el conjunto de ciudades o nodos. Los nodos est�n numerados de {1, ..., n},
- c(i,j) es el coste que se produce al ir de la ciudad i a la j,
- x(i,j)= 1 si el arco (i, j) esta en el grafo y x(i,j) = 0 si el arco no esta en el grafo,
*/
/*
TO-DO:
1- Separar el programa en dos partes: .mod con el ejecutable y .dat con los datos a leer.
Esto implica que n se debe obtener despues de leer el .dat

2- Si el .dat tiene la posicion de las ciudades (x, y) o (latitud, longitud) entonces:
a) Calcular n
b) Calcular distancia entre nodos
c) Al terminar el calculo mostrar una grafica con la posicion relativa de cada nodo y
mostrar ademas la ruta optima
*/

# DECLARACION DE VARIABLES ---------------
# n = numero de nodos o ciudades
param n, integer, >= 3;

# N = conjunto de todos los nodos
set N := 1..n;

# E = conjunto todos de arcos
set E, within N cross N;

# c[i,j] = distancia del nodo i al j 
param c{(i,j) in E};

# x[i,j] muestra si hay una conexion del nodo i al nodo j.
# x[i,j] = 1 si el arco (i, j) esta en el grafo y x[i,j] = 0 si ese arco no esta en el grafo,
var x{(i,j) in E}, binary;

# u[i] es la posici�n del nodo i dentro de la ruta, con i={1, ..., n}
# var u{(i) in N}, integer; No es necesario que sea integer
var u{i in N} >= 0;

# N_desde_2_hasta_n = Conjunto de nodos desde 2 .. n. Se usa para la restriccion 3 basadas en las de MTZ
set N_desde_2_hasta_n := 2..n;

# FUNCION OBJETIVO Y RESTRICCIONES ---------------
# La funcion objetivo minimiza el costo (longitud) del camino recorrido
minimize zObjetivo: sum{(i,j) in E} c[i,j] * x[i,j];

# Restriccion 1: El viajante abandona cada nodo exactamente una vez 
s.t. saliente{i in N}: sum{(i,j) in E : i != j} x[i,j] = 1;

# Restriccion 2: El viajante entra en cada nodo exactamente una vez
s.t. entrante{j in N}: sum{(i,j) in E : j != i} x[i,j] = 1;

/*
Sin embargo, con estas restricciones y la condici�n binaria de las variables x(i,j), 
no es suficiente para garantizar que las soluciones factibles son son ciclos cerrados en G. 
Es posible por tanto, que aparezca una soluci�n formada por subtours (no conectadas entre s�)
y que cumplan las restricciones anteriores. Es por ello, por lo que es necesario 
a�adir m�s restricciones que eviten la formaci�n de subtours.

Restriccion 3: Basada en la de Miller, Tucker y Zemlin (MTZ)
u(j) >= u(i) + 2 - n (1 - x(i,j)) - x(i,j) para i != 1, j != 1, i != j
*/

# Restriccion 3: MTZ
# Formulacion Orman Willians Paul 2004
#s.t. posicion{i in N_desde_2_hasta_n, j in N_desde_2_hasta_n : i != j}: 
#    u[i]-u[j]+n*x[i,j] <= (n-1);
s.t. posicion{i in N_desde_2_hasta_n, j in N_desde_2_hasta_n : i != j}: 
    u[i]-u[j]+1 <= (n-1)*(1-x[i,j]);

# RESOLUCION 
solve;

# MOSTRAR DATOS E INFO ---------------
printf "\n\nEl recorrido optimo tiene un coste %d\n\n",
   sum{(i,j) in E} c[i,j] * x[i,j];
printf("Nodo Origen   Nodo destino   Distancia   Orden nodo\n");
printf{(i,j) in E: x[i,j]} "    %3d         %3d       %8g           %3d\n",
   i, j, c[i,j], u[i];
/*
printf("Nodo Origen   Nodo destino   Distancia   Orden nodo   Conexion\n");
printf{(i,j) in E: i!=j} "    %3d         %3d       %8g        %3d        %3d\n",
   i, j, c[i,j], u[i], x[i,j];
*/

# DATOS USADOS EN ESTE PROBLEMA ---------------
data;

# La solucion optima es 32
param n := 10;

param : E : c :=
    1  2  7
    1  3  9
    1  4  8
    1  5  4
    1  6  3
    1  7  7
    1  8  7
    1  9  8
    1  10  5
    2  1  7
    2  3  4
    2  4  4
    2  5  9
    2  6  8
    2  7  4
    2  8  2
    2  9  1
    2  10  8
    3  1  9
    3  2  4
    3  4  8
    3  5  9
    3  6  8
    3  7  8
    3  8  2
    3  9  3
    3  10  11
    4  1  8
    4  2  4
    4  3  8
    4  5  11
    4  6  10
    4  7  1
    4  8  6
    4  9  5
    4  10  6
    5  1  4
    5  2  9
    5  3  9
    5  4  11
    5  6  1
    5  7  11
    5  8  8
    5  9  9
    5  10  9
    6  1  3
    6  2  8
    6  3  8
    6  4  10
    6  5  1
    6  7  9
    6  8  7
    6  9  8
    6  10  8
    7  1  7
    7  2  4
    7  3  8
    7  4  1
    7  5  11
    7  6  9
    7  8  6
    7  9  5
    7  10  5
    8  1  7
    8  2  2
    8  3  2
    8  4  6
    8  5  8
    8  6  7
    8  7  6
    8  9  1
    8  10  9
    9  1  8
    9  2  1
    9  3  3
    9  4  5
    9  5  9
    9  6  8
    9  7  5
    9  8  1
    9  10  9
    10  1  5
    10  2  8
    10  3  11
    10  4  6
    10  5  9
    10  6  8
    10  7  5
    10  8  9
    10  9  9
;
end;
