from Fonctions.data.importData import *
from Fonctions.getters import *
from Fonctions.converter import *

def isRetour(trajet):
    """
    Méthode qui inverse le service receveur et le service de provenance si le trajet sélectionné est un retour
    """
    if trajet["Retour"]=="1":
        tmp =  trajet["ID service receveur"]
        trajet["ID service receveur"]=trajet["ID service provenance"]
        trajet["ID service provenance"]=tmp

def affecterTempsMoyen(trajet):
    """
    Methode pour affecter le temps moyen d'un trajet en fonction de la matrice de temps 
    """
    if trajet["ID service provenance"]!=None and trajet["ID service receveur"]!=None:
        trajet["Temps moy"]=getTempsMoyenInterService(trajet["ID service provenance"],trajet["ID service receveur"])
    else:
        print("Pour le trajet n°",trajet["ID"]," le service de provenance ou de destination n'est pas défini ")


def affecterPriorite(trajet): 
    """
    Methode pour affecter la priorite d'un trajet en fonction des services de destinations 
    """   
    for s in serv_data :
        if trajet["ID service receveur"]==s["id_service"] and trajet["Retour"] == "0" :
            trajet["priorite"]=s["destination_prio"]



def affecterHeureDepart(trajet):
    """
    Methode pour affecter l'heure de départ ideal du service du provenance du trajet pôur atteindre le service de destination à l'heure de rdv prévu
    """
    if trajet["Heure de RDV"] != None and trajet["Temps moy"]!=None :
        heureIdealeCalc=intSecondes_to_heure(heure_to_intSecondes(trajet["Heure de RDV"])-trajet["Temps moy"])
        trajet["heure_depart"]= heureIdealeCalc
    else:
        print("L'heure de rdv ou le temps moyen du trajet n'est pas renseigné")

def recupTravailBrancardier():
    """
    Méthode pour récupérer le temps de travail total d'un brancardier sur sa journée de travail
    """
    for b in bra_data :
        for b2 in tot_bra_data:
            if b["id"]==b2["ID"]:
                b2["Travail Cumulé"]=intSecondes_to_heure(int(b["travail_cumule"]))
