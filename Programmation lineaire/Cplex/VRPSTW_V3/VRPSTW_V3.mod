/*********************************************
 * OPL 22.1.0.0 Model
 * Author: nrogers
 * Creation Date: 27 juil. 2022 at 10:04:50
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
int Dmin[N] = ...; // Dur�e minimale des missions
int Dmax[N] = ...; // Dur�e maximale des missions

int Hdeb_mat[B] = ...; // Dur�e minimale des missions
int Hfin_mat[B] = ...; // Dur�e maximale des missions
int Hdeb_apm[B] = ...; // Dur�e minimale des missions
int Hfin_apm[B] = ...; // Dur�e maximale des missions
int TraMax[B] = ...; // tps de travail maximal d'un brancardier

int Dmoyen[N][N] = ...; // Dur�e moyenne entre les missions (matrice des temps)

int M = 100000;

//*-------------------------------------------- Set of variables ----------------------------------------------*//
// Variables de temps
dvar int+ Tdep[N][B];  //heure de d�part de la mission i pour le brancardier k

dvar int+ e[N][B]; // heure de d�part (d�but de mission) au plus t�t (d�pend du bran car Tdep peut varier en fonction des bran)
dvar int+ l[N][B]; // heure de d�part (d�but de mission) au plus tard (d�pend du bran car Tdep peut varier en fonction des bran)
 
dvar boolean x[N][N][B]; // Choix du brancardier k pour j apr�s i 

dvar int+ s_moins[N][B]; // penalit� n�gative tps de d�part au plus t�t
dvar int+ s_plus[N][B]; // p�nalit� positive tps de d�part au plus t�t 

dvar int+ f_plus[N][B]; // p�nalit� positive tps de d�part au plus tard
dvar int+ f_moins[N][B]; // p�nalit� n�gative tps de d�part au plus tard

dvar int+ t_plus[N]; // p�nalit� positive tps de travail d'un brancardier
dvar int+ t_moins[N]; // p�nalit� n�gative tps de travail d'un brancardier

//dvar int+ g_plus[N]; // p�nalit� positive tps de rdv

dvar int+ d[B]; // tps travaill� des brancardiers


//*------------------------------- Objective function - Min de Temps trajet � vide -----------------------------*//
//
minimize (sum(i in N, k in B) (s_plus[i][k] + s_moins[i][k]) + 20 * sum(j in N, k in B) (f_plus[j][k] + f_moins[j][k]) + 10 * sum(k in N) (t_plus[k] + t_moins[k]));// + 20 * sum(j in N) g_plus[j]);



//*------------------------------------------- set of constraints ----------------------------------------------*//
subject to {

c1: // On d�finit l'heure de d�part au plus t�t
	forall(i in N, k in B) 
		e[i][k] + s_moins[i][k] - s_plus[i][k] >= Trdv[i] - Dmax[i];
		
c2: // On d�finit l'heure de d�part au plus tard
	forall(i in N, k in B) 
		l[i][k] + f_moins[i][k] - f_plus[i][k] <= Trdv[i] - Dmin[i];
		
c3: // On d�finit un temps de travail �quitable
	forall(i in B, j in B) // coupl�e avec c17, inutile toute seule
		d[i] + t_moins[i] - t_plus[i] == d[j] + t_moins[j] - t_plus[j];
		
c4: // d�part au plus t�t ne peut pas �tre apr�s la fin de la journ�e
	forall(i in N, k in B)
	  	l[i][k] <= Hfin_apm[k];

c5: // d�part au plus t�t ne peut pas �tre avant le d�but de la journ�e
	forall(i in N, k in B)
	  	e[i][k] >= Hdeb_mat[k];

c6: // heure de d�part apr�s l'heure de d�part au plus t�t
	forall(i in N: i>0, k in B)
	  	e[i][k] <= Tdep[i][k];

c7: // heure de d�part avant l'heure de d�part au plus tard
	forall(i in N: i>0, k in B)
	  	l[i][k] >= Tdep[i][k];
	  	
c8: // un seul brancardier arrive � une mission n�ccessitant qu'un seul brancardier
	forall(j in N1)
	  	sum(i in N: i!=j, k in B) x[i][j][k] == 1;
	  	
c9: // un seul brancardier part d'une mission n�ccessitant qu'un seul brancardier
	forall(i in N1)
	  	sum(j in N: i!=j, k in B) x[i][j][k] == 1;

c10: // exactement 2 brancardiers arrivent � une mission n�ccessitant 2 brancardiers
	forall(j in N2)
	  	sum(i in N: i!=j, k in B) x[i][j][k] == 2;
	  	
c11: // exactement 2 brancardiers partent d'une mission n�ccessitant 2 brancardiers
	forall(i in N2)
	  	sum(j in N: i!=j, k in B) x[i][j][k] == 2;

c12: // il y a autant de brancardiers arrivant � une mission que de brancardiers qui en parten
	forall(h in N, k in B)
	  	sum(i in N) x[i][h][k] - sum(j in N) x[h][j][k] == 0;

c13: // Ne pas d�passer le temps de travail maximal
	forall(k in B)
	  	sum(i in N, j in N: j != i) ((D[i] + Dmoyen[i][j]) * x[i][j][k]) <= TraMax[k];

c14: // Le temps de d�part (commencement) d'une mission est adapt�e par rapport au temps de rdv de la mission pr�c�dente
	forall(i in N, j in N: j>0, k in B)
	  	(Trdv[i] + Dmoyen[i][j]) + (x[i][j][k] - 1) * M <= Tdep[j][k];
	  	
c15: // Le temps de d�part (commencement) d'une mission est adapt�e par rapport au temps de rdv
	forall(i in N, j in N: j>0, k in B)
	  	(Trdv[j] - D[j]) >= Tdep[j][k] + (x[i][j][k] - 1) * M;

c16: // assurer qu'un brancardier retourne au d�p�t (mission 0)
	forall(k in B)
	  	sum(i in N: i != 0) x[i][0][k] == 1;

/*c17: // rajoute beaucoup de temps de calcul --> charge de travail similaires pour tous les brancardiers (avec c3)
	forall(k in B)
		d[k] == sum(i in N: i > 0, j in N: j != i) (D[i] + Dmoyen[i][j]) * x[i][j][k];*/

c17bis: // rajoute beaucoup moins de temps calcul que c17 --> donne le m�me nombre de trajets aux brancardiers
	forall(k in B)
		d[k] == sum(i in N: i > 0, j in N: j != i) x[i][j][k];

c18: // trajet ne se fait que dans un sens
	forall(i in N, j in N, k in B)
	  	x[i][j][k] + x[j][i][k] <= 1;

c21: // �vite les d�parts apr�s le Trdv pour cause de d�but de travail plus tard
	forall(i in N, j in N: j!=0, k in B)
	  	Trdv[j] >= Hdeb_mat[k] * x[i][j][k];

c24: // pas de travail pendant la pause d�jeuner
	forall(i in N, j in N, k in B)
	  	((Tdep[i][k] <= Hfin_mat[k]) && (Trdv[i] * x[i][j][k] <= Hfin_mat[k])) || ((Tdep[i][k] >= Hdeb_apm[k]) && (Trdv[i] >= Hdeb_apm[k]));

}




//*------------------------------------------- Retrieving data ----------------------------------------------*//

//R�cup�ration du nombre de trajet global
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

//Cr�ation des variables pour les r�sultats
range r = 1..countAll;		//cr�ation de la liste it�rable sur le nombre de trajet
int m1[r];				//liste des missions de d�part
int m2[r];				//liste des missions d'arriv�e
int bran[r];			//liste des brancardiers affect�s
int tdep[r]; 			//liste des heures de d�part
int tdep2[r]; 		//liste des heures de d�part
int trdv[r]; 		//liste des heures de d�part
int trdv2[r]; 		//liste des heures de d�part


//Titre des colones du excel
string md = "Miss_i";		
string ma = "Miss_j";		
string b = "Brancardier";
string ti = "Tdep_i";
string tj = "Tdep_j";
string trdvi = "Trdv_i";
string trdvj = "Trdv_j";


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
          trdv2[indice] = Trdv[j];
          indice = indice + 1;
        }
      }
    }
  }
}  
