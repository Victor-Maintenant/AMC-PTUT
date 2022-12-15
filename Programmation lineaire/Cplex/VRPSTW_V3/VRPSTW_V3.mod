/*********************************************
 * OPL 22.1.0.0 Model
 * Author: nrogers
 * Creation Date: 27 juil. 2022 at 10:04:50
 *********************************************/

 
//*------------------------------------------ Set of parameters ------------------------------------------------*//

int NbMissions = ...; // Nombre de missions
int NbMissions1 = ...; // Nombre de missions à 1 brancardier
int NbBrancardiers = ...; // Nombre de brancardiers

range N = 0..NbMissions; // Ensemble des missions y compris la mission 0 (dépot)
range B = 1..NbBrancardiers; // Ensemble des brancardiers

range N1 = 1..NbMissions1; 			 // ensemble des missions à un brancardier
range N2 = NbMissions1+1..NbMissions; // ensemble des missions à deux brancardiers

int Trdv[N] = ...; // Heures de rdv des missions

int D[N] = ...; // Durée estimée des missions
int Dmin[N] = ...; // Durée minimale des missions
int Dmax[N] = ...; // Durée maximale des missions

int Hdeb_mat[B] = ...; // Durée minimale des missions
int Hfin_mat[B] = ...; // Durée maximale des missions
int Hdeb_apm[B] = ...; // Durée minimale des missions
int Hfin_apm[B] = ...; // Durée maximale des missions
int TraMax[B] = ...; // tps de travail maximal d'un brancardier

int Dmoyen[N][N] = ...; // Durée moyenne entre les missions (matrice des temps)

int M = 100000;

//*-------------------------------------------- Set of variables ----------------------------------------------*//
// Variables de temps
dvar int+ Tdep[N][B];  //heure de départ de la mission i pour le brancardier k

dvar int+ e[N][B]; // heure de départ (début de mission) au plus tôt (dépend du bran car Tdep peut varier en fonction des bran)
dvar int+ l[N][B]; // heure de départ (début de mission) au plus tard (dépend du bran car Tdep peut varier en fonction des bran)
 
dvar boolean x[N][N][B]; // Choix du brancardier k pour j après i 

dvar int+ s_moins[N][B]; // penalité négative tps de départ au plus tôt
dvar int+ s_plus[N][B]; // pénalité positive tps de départ au plus tôt 

dvar int+ f_plus[N][B]; // pénalité positive tps de départ au plus tard
dvar int+ f_moins[N][B]; // pénalité négative tps de départ au plus tard

dvar int+ t_plus[N]; // pénalité positive tps de travail d'un brancardier
dvar int+ t_moins[N]; // pénalité négative tps de travail d'un brancardier

//dvar int+ g_plus[N]; // pénalité positive tps de rdv

dvar int+ d[B]; // tps travaillé des brancardiers


//*------------------------------- Objective function - Min de Temps trajet à vide -----------------------------*//
//
minimize (sum(i in N, k in B) (s_plus[i][k] + s_moins[i][k]) + 20 * sum(j in N, k in B) (f_plus[j][k] + f_moins[j][k]) + 10 * sum(k in N) (t_plus[k] + t_moins[k]));// + 20 * sum(j in N) g_plus[j]);



//*------------------------------------------- set of constraints ----------------------------------------------*//
subject to {

c1: // On définit l'heure de départ au plus tôt
	forall(i in N, k in B) 
		e[i][k] + s_moins[i][k] - s_plus[i][k] >= Trdv[i] - Dmax[i];
		
c2: // On définit l'heure de départ au plus tard
	forall(i in N, k in B) 
		l[i][k] + f_moins[i][k] - f_plus[i][k] <= Trdv[i] - Dmin[i];
		
c3: // On définit un temps de travail équitable
	forall(i in B, j in B) // couplée avec c17, inutile toute seule
		d[i] + t_moins[i] - t_plus[i] == d[j] + t_moins[j] - t_plus[j];
		
c4: // départ au plus tôt ne peut pas être après la fin de la journée
	forall(i in N, k in B)
	  	l[i][k] <= Hfin_apm[k];

c5: // départ au plus tôt ne peut pas être avant le début de la journée
	forall(i in N, k in B)
	  	e[i][k] >= Hdeb_mat[k];

c6: // heure de départ après l'heure de départ au plus tôt
	forall(i in N: i>0, k in B)
	  	e[i][k] <= Tdep[i][k];

c7: // heure de départ avant l'heure de départ au plus tard
	forall(i in N: i>0, k in B)
	  	l[i][k] >= Tdep[i][k];
	  	
c8: // un seul brancardier arrive à une mission néccessitant qu'un seul brancardier
	forall(j in N1)
	  	sum(i in N: i!=j, k in B) x[i][j][k] == 1;
	  	
c9: // un seul brancardier part d'une mission néccessitant qu'un seul brancardier
	forall(i in N1)
	  	sum(j in N: i!=j, k in B) x[i][j][k] == 1;

c10: // exactement 2 brancardiers arrivent à une mission néccessitant 2 brancardiers
	forall(j in N2)
	  	sum(i in N: i!=j, k in B) x[i][j][k] == 2;
	  	
c11: // exactement 2 brancardiers partent d'une mission néccessitant 2 brancardiers
	forall(i in N2)
	  	sum(j in N: i!=j, k in B) x[i][j][k] == 2;

c12: // il y a autant de brancardiers arrivant à une mission que de brancardiers qui en parten
	forall(h in N, k in B)
	  	sum(i in N) x[i][h][k] - sum(j in N) x[h][j][k] == 0;

c13: // Ne pas dépasser le temps de travail maximal
	forall(k in B)
	  	sum(i in N, j in N: j != i) ((D[i] + Dmoyen[i][j]) * x[i][j][k]) <= TraMax[k];

c14: // Le temps de départ (commencement) d'une mission est adaptée par rapport au temps de rdv de la mission précédente
	forall(i in N, j in N: j>0, k in B)
	  	(Trdv[i] + Dmoyen[i][j]) + (x[i][j][k] - 1) * M <= Tdep[j][k];
	  	
c15: // Le temps de départ (commencement) d'une mission est adaptée par rapport au temps de rdv
	forall(i in N, j in N: j>0, k in B)
	  	(Trdv[j] - D[j]) >= Tdep[j][k] + (x[i][j][k] - 1) * M;

c16: // assurer qu'un brancardier retourne au dépôt (mission 0)
	forall(k in B)
	  	sum(i in N: i != 0) x[i][0][k] == 1;

/*c17: // rajoute beaucoup de temps de calcul --> charge de travail similaires pour tous les brancardiers (avec c3)
	forall(k in B)
		d[k] == sum(i in N: i > 0, j in N: j != i) (D[i] + Dmoyen[i][j]) * x[i][j][k];*/

c17bis: // rajoute beaucoup moins de temps calcul que c17 --> donne le même nombre de trajets aux brancardiers
	forall(k in B)
		d[k] == sum(i in N: i > 0, j in N: j != i) x[i][j][k];

c18: // trajet ne se fait que dans un sens
	forall(i in N, j in N, k in B)
	  	x[i][j][k] + x[j][i][k] <= 1;

c21: // évite les départs après le Trdv pour cause de début de travail plus tard
	forall(i in N, j in N: j!=0, k in B)
	  	Trdv[j] >= Hdeb_mat[k] * x[i][j][k];

c24: // pas de travail pendant la pause déjeuner
	forall(i in N, j in N, k in B)
	  	((Tdep[i][k] <= Hfin_mat[k]) && (Trdv[i] * x[i][j][k] <= Hfin_mat[k])) || ((Tdep[i][k] >= Hdeb_apm[k]) && (Trdv[i] >= Hdeb_apm[k]));

}




//*------------------------------------------- Retrieving data ----------------------------------------------*//

//Récupération du nombre de trajet global
int countAll = 0;	
execute {
  for ( var i in N) {
    for ( var j in N) {
      if (i != j) {
        for ( var k in B) {
          if (x[i][j][k] == 1) {
			countAll = countAll +1;
          }
        }
      }
    }
  }
}  

//Création des variables pour les résultats
range r = 1..countAll;		//création de la liste itérable sur le nombre de trajet
int m1[r];				//liste des missions de départ
int m2[r];				//liste des missions d'arrivée
int bran[r];			//liste des brancardiers affectés
int tdep[r]; 			//liste des heures de départ
int tdep2[r]; 		//liste des heures de départ
int trdv[r]; 		//liste des heures de départ
int trdv2[r]; 		//liste des heures de départ


//Titre des colones du excel
string md = "Miss_i";		
string ma = "Miss_j";		
string b = "Brancardier";
string ti = "Tdep_i";
string tj = "Tdep_j";
string trdvi = "Trdv_i";
string trdvj = "Trdv_j";


//Implémentation des variables 
int indice = 1;
execute{
  for ( var k in B) {
    for ( var i in N) {
      for ( var j in N) {
        if (x[i][j][k] == 1) {
          m1[indice] = i;
          m2[indice] = j;
          bran[indice] = k;
          tdep[indice] = Tdep[i][k];
          tdep2[indice] = Tdep[j][k];
          trdv[indice] = Trdv[i];
          trdv2[indice] = Trdv[j];
          indice = indice + 1;
        }
      }
    }
  }
}  
