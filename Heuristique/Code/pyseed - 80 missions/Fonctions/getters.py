from Fonctions.data.importData import *
from Fonctions.converter import *

def getTempsMoyenInterService(serviceA, serviceB) :
    """
    Methode pour obtenir le temps moyen du serviceA vers le serviceB
    """
    if serviceA!=serviceB:
        for t in tmps_data:
            if int(serviceA)==int(t["serviceProvenance"]) and int(serviceB)==int(t["serviceDestination"]):
                res = int(t["temps_moyen"])*60
                return(res)
        return 600
    else:
        return 0

def getDelaiLocalisation(brancardier, service) -> int:
    """
    Methode donnant le delai entre le depart du brancardier depuis le service où il est localise vers le service de départ d'un brancardier
    """
    if brancardier["localisation"]==service :
        return 0
    else :
        return getTempsMoyenInterService(brancardier["localisation"],service)
        

def getHeureDepartBrancardier(trajet, brancardier):
    """
    Methode donnant l'heure au brancardier pour partir du service ou il est localise vers le service de depart d'un brancardier
    \n"A quelle heure doit partir le brancardier de sa position pour etre au service de départ de la demande selon l'heure de départ prévu"
    """
    if trajet["heure_depart"]!=None:
        heuredpartdepuisservicedepart=heure_to_intSecondes(trajet["heure_depart"])
        delaipourrejoindreservicedepart=getDelaiLocalisation(brancardier,trajet["ID service provenance"])
        res=intSecondes_to_heure(heuredpartdepuisservicedepart-delaipourrejoindreservicedepart)
        return res
    else:
        print("heure de depart non défini, impossible de calculer getHeureDepartBrancardier")


def getModeTransport(trajet):
    """
    Donne le moyen de transport d'un trajet
    """
    return str(trajet["Mode de transport"])