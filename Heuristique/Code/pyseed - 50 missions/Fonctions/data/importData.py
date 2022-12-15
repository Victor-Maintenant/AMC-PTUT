import csv
# On initialise les listes qui contiendront les trajets, les brancardiers etc...
tra_data = [] # Liste des trajets
bra_data=[] # Liste des brancardiers
tmps_data=[] # Liste des temps moyens
journee_data = [] # Liste de la journée type (à Maubeuge pour l'exemple)
tot_bra_data = [] # Liste des brancardiers affectés
serv_data = [] # Liste des services

# On initialise les en-têtes des tableaux Excel
headers_traj = [] 
headers_bran = []
headers_tmps = []
headers_tot_bra = []

# On charge les fichiers CSV du sous-dossier "Scénario" pour récupérer les en-têtes et les valeurs
with open('Scenario/journee_type.csv', newline='') as f :
    headers_traj= next(f).rstrip().split(";")
    data = csv.DictReader(f, fieldnames=headers_traj, delimiter=";" )
    for item in data:
        tra_data.append(dict(item))

with open('Scenario/brancardiers2.csv', newline='') as f :
    headers_bran= next(f).rstrip().split(";")
    data = csv.DictReader(f, fieldnames=headers_bran, delimiter=";" )
    i = 1
    for item in data:
        if(i<=5):
            bra_data.append(dict(item))
        i+=1    

with open('Scenario/matrice_tempsMoyen.csv', newline='') as f :
    headers_tmps= next(f).rstrip().split(";")
    data = csv.DictReader(f, fieldnames=headers_tmps, delimiter=";" )
    for item in data:
        tmps_data.append(dict(item))

with open('Scenario/brancardiers2.csv', newline='') as f :
    headers_tot_bra= ['ID', 'Nom brancardier', 'Trajets', 'Nombre de transports', 'Travail Cumulé']
    data = csv.DictReader(f, fieldnames=headers_tot_bra, delimiter=";" )
    i = 1
    for item in data:
        if(i<=5):
            tot_bra_data.append(dict(item))
        i+=1
    for t in tot_bra_data :
        t["Trajets"] = ""
        t["Nombre de transports"] = ""
        t["Travail Cumulé"] = ""
        t.pop(None,0)


with open('Scenario/services.csv', newline='') as f :
    headers_serv= next(f).rstrip().split(";")
    data = csv.DictReader(f, fieldnames=headers_serv, delimiter=";" )
    for item in data:
        serv_data.append(dict(item))

for t in tra_data:
    if t["priorite"] == "" :
        t["priorite"] = "6"

def exportALL():
    with open('Resultat/RES_brancardiers.csv', 'wt',newline='') as fi :
        csv_writer = csv.DictWriter(fi, fieldnames=headers_bran, delimiter=';')
        csv_writer.writeheader()
        csv_writer.writerows(bra_data)

    with open('Resultat/RES_tmps.csv', 'wt',newline='') as fi :
        csv_writer = csv.DictWriter(fi, fieldnames=headers_tmps, delimiter=';')
        csv_writer.writeheader()
        csv_writer.writerows(tmps_data)

    with open('Resultat/RES_Maubeuge_tot.csv', 'wt',newline='') as fi :
        csv_writer = csv.DictWriter(fi, fieldnames=headers_traj, delimiter=';')
        csv_writer.writeheader()
        csv_writer.writerows(tra_data)

    with open('Resultat/RES_Maubeuge_Brancardiers.csv', 'wt',newline='') as fi :
        csv_writer = csv.DictWriter(fi, fieldnames=headers_tot_bra, delimiter=';')
        csv_writer.writeheader()
        csv_writer.writerows(tot_bra_data)
