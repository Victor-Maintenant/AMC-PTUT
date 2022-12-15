/*********************************************
 * OPL 22.1.0.0 Model
 * Author: nrogers
 * Creation Date: 13 juil. 2022 at 10:32:26
 *********************************************/

 
//*------------------------------------------ Set of parameters ------------------------------------------------*//

int NbMissions = ...; // Nombre de missions
int NbMissions1 = ...; // Nombre de missions � 1 brancardier
int NbBrancardiers = ...; // Nombre de brancardiers

range N = 0..NbMissions; // Ensemble des missions y compris la mission 0 (d�pot)
range B = 1..NbBrancardiers; // Ensemble des brancardiers

range N1 = 1..NbMissions1; 			 // ensemble des missions � un brancardier
range N2 = NbMissions1+1..NbMissions; // ensemble des missions � deux brancardiers

int Trdv[N] = ...; // Heures de rdv des missions

int D[N] = ...; // Dur�e estim�e des missions

int Hdeb_mat[B] = ...; // Dur�e minimale des missions
int Hfin_mat[B] = ...; // Dur�e maximale des missions
int Hdeb_apm[B] = ...; // Dur�e minimale des missions
int Hfin_apm[B] = ...; // Dur�e maximale des missions
int TraMax[B] = ...; // tps de travail maximal d'un brancardier

int Dmoyen[N][N] = ...; // Dur�e moyenne entre les missions (matrice des temps)

int M = 100000;
int R[N] = ...;

//*-------------------------------------------- Set of variables ----------------------------------------------*//
// Variables de temps
dvar int+ Tdep[N][B];  //heure de d�part de la mission i pour le brancardier k
dvar int+ Trdv2[N][B];
 
dvar boolean x[N][N][B]; // Choix du brancardier k pour j apr�s i 

dvar int+ t_plus[B]; // p�nalit� positive tps de travail d'un brancardier
dvar int+ t_moins[B]; // p�nalit� n�gative tps de travail d'un brancardier

dvar int+ late[N][B]; // p�nalit� positive tps de rdv

dvar int+ d[B]; // tps travaill� des brancardiers


//*------------------------------- Objective function - Min le retard et ajuster le travail -----------------------------*//
//
minimize (sum(i in N, j in N, k in B) Dmoyen[i][j]*x[i][j][k]);


//*------------------------------------------- set of constraints ----------------------------------------------*//
subject to {

c1:
	forall(j in N1) 
	  	sum(i in N: i!=j, k in B) x[i][j][k] == 1;
	  	
c2:
	forall(i in N1) 
	  	sum(j in N: i!=j, k in B) x[i][j][k] == 1;

c3:
	forall(j in N2) 
	  	sum(i in N: i!=j, k in B) x[i][j][k] == 2;
	  	
c4:
	forall(i in N2) 
	  	sum(j in N: i!=j, k in B) x[i][j][k] == 2;
	  	
c5:
	forall(h in N, k in B)
	  	sum(j in N: j!=h) x[h][j][k] == sum(i in N:i!=h) x[i][h][k];

c6:
	forall(k in B)
	  	sum(i in N: i != 0) x[0][i][k] == 1;
	  		  		  
/*c7:
	forall(k in B, l in B:k!=l) // coupl�e avec c8, inutile toute seule
		d[k] + t_moins[k] - t_plus[k] == d[l] + t_moins[l] - t_plus[l];
		
/*c8: // rajoute beaucoup de temps de calcul: 2min - 5bran;  - 7bran --> charge de travail similaires pour tous les brancardiers (avec c3)
	forall(k in B)
		sum(i in N: i > 0, j in N: j != i) (D[i] + Dmoyen[i][j]) * x[i][j][k] == d[k];*/

/*c9: // rajoute beaucoup moins de temps calcul que c8 --> donne le m�me nombre de trajets aux brancardiers
	forall(k in B)
		sum(i in N:i>0, j in N:(j!=0 && j!=i)) x[i][j][k] == d[k]; */
		
c10:
	forall(k in B)
	  	sum(i in N, j in N: j != i) ((D[i] + Dmoyen[i][j]) * x[i][j][k]) <= TraMax[k]; 	

c11:
	forall(i in N: i!=0, j in N:(j!=0 && j!=i), k in B)
	  	(Trdv[i] + Dmoyen[i][j]) + (x[i][j][k]-1) * M <= Tdep[j][k];

c12:
	forall(i in N:i!=0, k in B)
	  	Tdep[i][k] <= Trdv[i]-D[i]+late[i][k];
	  		 	

c13: 
	forall(i in N, k in B)
	  	Trdv2[i][k] >= Trdv[i] + late[i][k];

/*c14:
	forall(i in N:i!=0, k in B)
	  	Trdv[i] <= Hfin_apm[k];

c15:
	forall(i in N: i!=0, j in N: j!=0, k in B)
	  	Tdep[i][k] >= Hdeb_mat[k];

c21: // Heure de rdv ne peut pas �tre avant que le brancardier ne commence � travailler
	forall(i in N, j in N:(j!=0 && j!=i), k in B)
	  	Trdv2[j][k] >= Hdeb_mat[k]* x[i][j][k];
  	
c17:
	forall(i in N, k in B)
	  	((Tdep[i][k] <= Hfin_mat[k] - D[i]) && (Trdv2[i][k] <= Hfin_mat[k])) || ((Tdep[i][k] >= Hdeb_apm[k]) && (Trdv2[i][k] >= Hdeb_apm[k] + D[i]));*/
	  	
c18:
	forall(i in N, j in N2:j!=i, k in B, l in B:l!=k)
	  	Tdep[j][k] <= Tdep[j][l] + M*(1-x[i][j][k]);

c19:
	forall(i in N:i!=0, j in N:j!=0, k in B)
	  	late[i][k] + M*(x[i][j][k] - 1) <= R[i];  

}

//R�cup�ration du nombre de trajet global
int countAll = 0;	
execute {
  for ( var i in N) {
	    for ( var j in N) {
	        for ( var k in B) {
	          if (x[i][j][k] == 1) {
				countAll = countAll +1;
	          }
	        }
	      }
	    }
	  
	 
}  

//Cr�ation des variables pour les r�sultats
range r = 1..countAll;		//cr�ation de la liste it�rable sur le nombre de trajet
int m1[r];				//liste des missions de d�part
int m2[r];				//liste des missions d'arriv�e
int bran[r];			//liste des brancardiers affect�s
int tdep[r]; 			//liste des heures de d�part
int tdep2[r]; 		//liste des heures de d�part
int trdv[r]; 		//liste des heures de d�part
int trdv2[r]; 		//liste des heures de d�part
int hfin_mat[r]; 		//liste des heures de d�part
int hdeb_apm[r]; 		//liste des heures de d�part


//Titre des colones du excel
string md = "Mission_depart";		
string ma = "Mission_arrivee";		
string b = "Brancardier";


//Impl�mentation des variables 
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

