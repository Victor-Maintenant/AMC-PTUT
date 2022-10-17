/*********************************************
 * OPL 22.1.0.0 Model
 * Author: nrogers
 * Creation Date: 13 juil. 2022 at 10:32:26
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
//int Z = 100;


//*-------------------------------------------- Set of variables ----------------------------------------------*//
// Variables de temps
dvar int+ Tdep[N][B];  //heure de départ de la mission i pour le brancardier k
dvar int+ Trdv2[N][B];

//dvar int+ e[N][B]; // heure de départ (début de mission) au plus tôt
//dvar int+ l[N][B]; // heure de départ (début de mission) au plus tard
 
dvar boolean x[N][N][B]; // Choix du brancardier k pour j après i 

/*dvar int+ s_moins[N][B]; // penalité négative tps de départ au plus tôt
dvar int+ s_plus[N][B]; // pénalité positive tps de départ au plus tôt 

dvar int+ f_plus[N][B]; // pénalité positive tps de départ au plus tard
dvar int+ f_moins[N][B]; // pénalité négative tps de départ au plus tard*/

dvar int+ t_plus[B]; // pénalité positive tps de travail d'un brancardier
dvar int+ t_moins[B]; // pénalité négative tps de travail d'un brancardier

dvar int+ late[N][B]; // pénalité positive tps de rdv

dvar int+ d[B]; // tps travaillé des brancardiers


//*------------------------------- Objective function - Min de Temps trajet à vide -----------------------------*//
//
minimize (sum(j in N, k in B) (late[j][k]) + sum(k in B) (t_plus[k] + t_moins[k]));


//*------------------------------------------- set of constraints ----------------------------------------------*//
subject to {

c0: 
	forall(i in N, k in B)
	  	Trdv2[i][k] - late[i][k] == Trdv[i];

/*c1:
	forall(i in N, k in B) 
		e[i][k] + s_moins[i][k] - s_plus[i][k] >= Trdv2[i][k] - Dmax[i];
		
c2:
	forall(i in N, k in B)
		l[i][k] + f_moins[i][k] - f_plus[i][k] <= Trdv2[i][k] - Dmin[i];*/
		
c3:
	forall(i in B, j in B) // couplée avec c17, inutile toute seule
		d[i] + t_moins[i] - t_plus[i] == d[j] + t_moins[j] - t_plus[j];
		
c4:
	forall(i in N, k in B)
	  	Trdv2[i][k] - late[i][k] <= Hfin_apm[k];

c5:
	forall(i in N, k in B)
	  	Tdep[i][k] >= Hdeb_mat[k];

/*c6:
	forall(i in N: i>0, k in B)
	  	e[i][k] <= Tdep[i][k];

c7:
	forall(i in N: i>0, k in B)
	  	l[i][k] >= Tdep[i][k];*/
	  	
c8:
	forall(j in N1) // Vérifier que c'est pas grave qu'il y ait pas la mission 0
	  	sum(i in N: i!=j, k in B) x[i][j][k] == 1;
	  	
c9:
	forall(i in N1) // Vérifier que c'est pas grave qu'il y ait pas la mission 0
	  	sum(j in N: i!=j, k in B) x[i][j][k] == 1;

c10:
	forall(j in N2) // Vérifier que c'est pas grave qu'il y ait pas la mission 0
	  	sum(i in N: i!=j, k in B) x[i][j][k] == 2;
	  	
c11:
	forall(i in N2) // Vérifier que c'est pas grave qu'il y ait pas la mission 0
	  	sum(j in N: i!=j, k in B) x[i][j][k] == 2;

c12:
	forall(h in N, k in B)
	  	sum(i in N) x[i][h][k] - sum(j in N) x[h][j][k] == 0;

c13:
	forall(k in B)
	  	sum(i in N, j in N: j != i) ((D[i] + Dmoyen[i][j]) * x[i][j][k]) <= TraMax[k];

c14:
	forall(i in N, j in N: j>0, k in B)
	  	(Trdv2[i][k] + Dmoyen[i][j]) + (x[i][j][k] - 1) * M <= Tdep[j][k];
	  	
c14bis:
	forall(i in N, j in N: j>0, k in B)
	  	(Trdv2[j][k] - D[j]) >= Tdep[j][k] + (x[i][j][k] - 1) * M;

c16: // make sure returns to 0
	forall(k in B)
	  	sum(i in N: i != 0) x[i][0][k] == 1;

/*c17: // rajoute beaucoup de temps de calcul: 2min - 5bran;  - 7bran --> charge de travail similaires pour tous les brancardiers (avec c3)
	forall(k in B)
		d[k] == sum(i in N: i > 0, j in N: j != i) (D[i] + Dmoyen[j][i]) * x[i][j][k];*/

c17bis: // rajoute beaucoup moins de temps calcul que c17 --> donne le même nombre de trajets aux brancardiers
	forall(k in B)
		d[k] == sum(i in N: i > 0, j in N: j != i) x[i][j][k];

c18: // trajet ne se fait que dans un sens
	forall(i in N, j in N, k in B)
	  	x[i][j][k] + x[j][i][k] <= 1;

c21: 
	forall(i in N, j in N: j!=0, k in B)
	  	Trdv2[j][k] >= Hdeb_mat[k] * x[i][j][k];
	  	
/*c23:
	forall(i in N, k in B)
	  	!((Tdep[i][k] <= Hdeb_apm[k]) && (Tdep[i][k] >= Hfin_mat[k])) && !((Trdv2[i][k] <= Hdeb_apm[k]) && (Trdv2[i][k] >= Hfin_mat[k]))*/
	  	
/*c26:
	forall(i in N, j in N, k in B)
	  	!((Trdv2[i][k] <= Hdeb_apm[k]) && (Trdv2[i][k] >= Hfin_mat[k]));*/
	  	
c24:
	forall(i in N, k in B)
	  	((Tdep[i][k] <= Hfin_mat[k] - D[i]) && (Trdv2[i][k] <= Hfin_mat[k])) || ((Tdep[i][k] >= Hdeb_apm[k]) && (Trdv2[i][k] >= Hdeb_apm[k] + D[i]));
/*c25:
	forall(i in N, j in N, k in B)
	  	(Tdep[i][k] <= Hfin_mat[k]) || (Tdep[i][k] >= Hdeb_apm[k]);
	  	
c27:
	forall(i in N, j in N, k in B)
	  	(Trdv2[i][k] <= Hfin_mat[k]) || (Trdv2[i][k] >= Hdeb_apm[k]);*/
	  	
c25:
	forall(i in N2, k in B, l in B)
	  Trdv2[i][k] == Trdv2[i][l];
	  

}

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
int hfin_mat[r]; 		//liste des heures de départ
int hdeb_apm[r]; 		//liste des heures de départ


//Titre des colones du excel
string md = "Mission_depart";		
string ma = "Mission_arrivee";		
string b = "Brancardier";


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
          trdv2[indice] = Trdv2[i][k];
          hfin_mat[indice] = Hfin_mat[k];
          hdeb_apm[indice] = Hdeb_apm[k];
          indice = indice + 1;
        }
      }
    }
  }
}  
