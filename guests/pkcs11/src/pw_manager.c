/*
 * Example Application:
 * A very rudimentary Password Manager,
 * that uses the Key Management Functionality
 */

#include "pw_manager.h"

#include <lib.h>
#include <types.h>

#include "pkcs11_library.h"

//#define DEBUG


struct pw_db {
	unsigned char url[256];
	unsigned char username[256];
	unsigned char password[32]; // Encrypted Password TODO: check length of this!!
	unsigned char iv[16];
	unsigned long encryption_key_handle;
	unsigned long trusted_key_handle;
	int index; // we only allow up to 32 passwords so far
}; //pw_db_t;

static const unsigned char cb[] = {
		0x00, 0x00, 0x00, 0x00,
		0x00, 0x00, 0x00, 0x00,
		0x00, 0x00, 0x00, 0x00,
		0x00, 0x00, 0x00, 0x01
};




/* -------  COMMANDS  -------- */

#define ADD_ENTRY 		1
#define REMOVE_ENTRY 	2
#define SHOW_ENTRIES 	3
#define GET_PASSWORD	4
#define EXPORT_ENTRY 	5
#define IMPORT_ENTRY	6
#define QUIT 			9






static void increment_nonce(unsigned char nonce[16]) {
	int i;
#ifdef DEBUG
	printf("Nonce init: ");
	print_hex(nonce, 16);
#endif
	for (i = 16; i > 0; i--) {
		if (++nonce[i-1] != 0)
			break;
	}
#ifdef DEBUG
	printf("Nonce incremented: ");
	print_hex(nonce, 16);
#endif
}


/* Initialize Token and Generate Master Key */
int init_pw_manager(struct pw_db database[32]) {

	/* all indices -1: no password stored */

	CK_RV rv;

	int i = 0;
	for (i = 0; i < 32; i ++) {
		database[i].index = -1;
	}

	CK_BYTE soPin[5];
	CK_BYTE userPin[5];

	printf("This is the first time you use the Password Manager.\n");

	C_Initialize(NULL);

	printf("SO PIN: ");
	fgets(soPin, 5);
	printf("\n");

	CK_SLOT_ID slotId= 1;
	CK_UTF8CHAR pLabel[16] = "PWManager Token";


	rv = C_InitToken(slotId, soPin, 4, pLabel);
	if (rv != CKR_OK)
		return rv;

	CK_SESSION_HANDLE hSession;
	CK_FLAGS flags = CKF_SERIAL_SESSION | CKF_RW_SESSION;
	rv = C_OpenSession(slotId, flags, NULL, NULL, &hSession);

	if (rv != CKR_OK)
		return rv;

	printf("Session opened: %d\n", hSession);

	/* Login as SO to generate TRUSTED key */
	rv = C_Login(hSession, CKU_SO, soPin, 4);
	if (rv != CKR_OK)
		return rv;

	printf("Generate Master Key, that encrypts your passwords...\n");

	CK_OBJECT_CLASS keyClass = CKO_SECRET_KEY;
	CK_KEY_TYPE keyType = CKK_AES;
	CK_MECHANISM mechanism = { CKM_AES_CTR, NULL_PTR, 0 };
	CK_BBOOL true = CK_TRUE;
	CK_OBJECT_HANDLE hTrustedKey, hUsageKey;

	/* Generate Trusted Key */
	CK_ATTRIBUTE wrappingTemplate[] = {
			{CKA_ENCRYPT, &true, sizeof(true)},
			{CKA_DECRYPT, &true, sizeof(true)},
			{CKA_SENSITIVE, &true, sizeof(true)},
			{CKA_EXTRACTABLE, &true, sizeof(true)},
			{CKA_WRAP_WITH_TRUSTED, &true, sizeof(true)}
	};
	CK_ATTRIBUTE keyTemplate[] = {
			{CKA_CLASS, &keyClass, sizeof(keyClass)},
			{CKA_KEY_TYPE, &keyType, sizeof(keyType)},
			{CKA_WRAP, &true, sizeof(true)},
			{CKA_UNWRAP, &true, sizeof(true)},
			{CKA_SENSITIVE, &true, sizeof(true)},
			{CKA_EXTRACTABLE, &true, sizeof(true)},
			{CKA_TRUSTED, &true, sizeof(true)},
			{CKA_WRAP_WITH_TRUSTED, &true, sizeof(true)},
			{CKA_WRAP_TEMPLATE, &wrappingTemplate, 5},
			{CKA_UNWRAP_TEMPLATE, &wrappingTemplate, 5}
	};

	rv  = C_GenerateKey(hSession, &mechanism, keyTemplate, 10, &hTrustedKey);
	if (rv != CKR_OK) {
		printf("Ooops, could not create Master Key. No Password Manager for you this time: %x\n", rv);
		return rv;
	}


	for (i = 0; i < 32; i++) {
		database[i].trusted_key_handle = hTrustedKey;
	}

	/* Initialize user PIN */
	printf("User PIN: ");
	fgets(userPin, 5);
	printf("\n");

	rv = C_InitPIN(hSession, userPin, 4);
	if (rv != CKR_OK)
		return rv;


	/* Switch to User */
	rv = C_Logout(hSession);
	if (rv != CKR_OK)
		return rv;

	rv = C_Login(hSession, CKU_USER, userPin, 4);
	if (rv != CKR_OK)
		return rv;
	return 0;
}

/* Add new Object to the database */
int encrypt_password(struct pw_db database[32], char url[256], char username[256], char password[16]) {
	if (url == NULL || username == NULL || password == NULL) {
		printf("You should use better parameters\n");
		return -1;
	}



	CK_RV rv;
	CK_SESSION_HANDLE hSession = 1;
	CK_OBJECT_CLASS keyClass = CKO_SECRET_KEY;
	CK_KEY_TYPE keyType = CKK_AES;
	CK_MECHANISM mechanism = { CKM_AES_CTR, NULL_PTR, 0 };
	CK_BBOOL true = CK_TRUE;
	CK_OBJECT_HANDLE hUsageKey;
	CK_BYTE password_encrypted[32];
	CK_ULONG len;

	CK_MECHANISM encryptMechanism;
	CK_AES_CTR_PARAMS ctrParams;

	unsigned char passwordEncrypted[32];


	int i = 0, index = -1;

	/* search for next free database entry */
	for(i = 0; i < 32; i ++) {
		if (database[i].index == -1) {
			index = i;
			break;
		}
	}

	if (index == -1) {
		printf("You already have 32 Passwords stored.\n");
		return -1; /* no free entry in database */
	}

	/* Generate Usage Key */
	CK_ATTRIBUTE usageKeyTemplate[] = {
			{CKA_CLASS, &keyClass, sizeof(keyClass)},
			{CKA_KEY_TYPE, &keyType, sizeof(keyType)},
			{CKA_ENCRYPT, &true, sizeof(true)},
			{CKA_DECRYPT, &true, sizeof(true)},
			{CKA_SENSITIVE, &true, sizeof(true)},
			{CKA_EXTRACTABLE, &true, sizeof(true)},
			{CKA_WRAP_WITH_TRUSTED, &true, sizeof(true)}
	};

	rv = C_GenerateKey(hSession, &mechanism, usageKeyTemplate, 7, &hUsageKey);
	if (rv != CKR_OK) {
		printf("Could not generate new usage key.\n");
		return -1;
	}


	// ensure nonce freshness
	for (i = 0; i < 4; i++) {
		increment_nonce(cb);
	}
	memcpy(ctrParams.cb, cb, 16);
	ctrParams.ulCounterBits = 128;

	encryptMechanism.mechanism = CKM_AES_CTR;
	encryptMechanism.pParameter = (CK_VOID_PTR) &ctrParams;
	encryptMechanism.ulParameterLen = 2;

	/* Encrypt the password with this usage key */
	//printf("pParameter Address: %x, CB parameter: %x \n", encryptMechanism.pParameter, cb);
	//if (encryptMechanism.pParameter == NULL)
	//	printf("pParameter is null, wtf\n", (uint32_t) encryptMechanism.pParameter);
	//if (cb == NULL)
	//	printf("CB is null, wtf wtf\n");
	rv = C_EncryptInit(hSession, &encryptMechanism, hUsageKey);
	if (rv != CKR_OK) {
		printf("Could not init Encrypt: %x\n", rv);
		return -1;
	}




	rv = C_Encrypt(hSession, password, 32, passwordEncrypted, &len);
	if (rv != CKR_OK) {
		printf("Could not encrypt your password :%x.\n", rv);
		return -1;
	}

	/* Fill database entry */
	database[index].encryption_key_handle = hUsageKey;
	strncpy(database[index].url, url, 256);
	strncpy(database[index].username, username, 256);
	memcpy(database[index].password, passwordEncrypted, 32);
	memcpy(database[index].iv, cb, 16);
	database[index].index = index;

	printf("Successfully added a password to the Password Manager!\n\n");
	return 0;

}

/* Print the password for a given databse entry */
int decrypt_password(struct pw_db database[32], int index) {
	if (index < 0 || index > 31) {
		printf("Choose a correct entry: %c.\n", index);
		return -1;
	}

	CK_RV rv;
	CK_SESSION_HANDLE hSession = 1;
	unsigned char password[32];
	CK_ULONG len;


	CK_MECHANISM decryptMechanism;
	CK_AES_CTR_PARAMS ctrParams;

	memcpy(ctrParams.cb, database[index].iv, 16);
	ctrParams.ulCounterBits = 128;

	decryptMechanism.mechanism = CKM_AES_CTR;
	decryptMechanism.pParameter = (CK_VOID_PTR) &ctrParams;
	decryptMechanism.ulParameterLen = 2;


	rv = C_DecryptInit(hSession, &decryptMechanism, database[index].encryption_key_handle);
	if (rv != CKR_OK) {
		printf("Return Value fail: %x\n");
		return rv;
	}

	rv = C_Decrypt(hSession, database[index].password, 32, password, &len);
	if (rv != CKR_OK) {
		printf("Failed to decrypt the password: %x\n", rv);
		return -1;
	}

	printf("\n####\n");
	printf("URL: %s\n", database[index].url);
	printf("Username: %s\n", database[index].username);
	printf("Password: %s\n", password);
	printf("####\n");
	return 0;
}

int delete_entry(struct pw_db database[32], int index) {
	if (index < 0 || index > 32) {
		printf("Choose a valid Entry\n");
		printf("%d\n", index);
		return -1;
	}

	database[index].index = -1;
	return 0;
}

int show_manager_state(struct pw_db database[32]) {
	int i;

		for (i = 0; i < 32; i ++) {
			if (database[i].index != -1) {
				printf("\n### Entry: %d\n", i);
				printf("URL: %s\n", database[i].url);
				printf("Username: %s\n", database[i].username);
				printf("Password encrypted:");
				print_hex(database[i].password, 16);
			}
		}
		return 0;
}


/* Exporting an Entry requires to wrap the specific key
 * used to encrypt the password
 */
int export_db_entry( struct pw_db database[32]) {
	unsigned char wrappedKey[16];
	unsigned long wrappedKeyLen;
	CK_RV rv;
	CK_SESSION_HANDLE hSession = 1;
	CK_MECHANISM wrapMechanism;
	CK_AES_CTR_PARAMS ctrParams;


	printf("\nPlease enter index of Entry you want to export\n");
	printf("Index: > ");
	int index = get_char() - '0';
	printf("%c\n\n", index);




	increment_nonce(cb);

	int i;
	for (i = 0; i < 100; i++) {
		increment_nonce(cb);

	}


	memcpy(ctrParams.cb, cb,  16);
	ctrParams.ulCounterBits = 128;

	wrapMechanism.mechanism = CKM_AES_CTR;
	wrapMechanism.pParameter = (CK_VOID_PTR) &ctrParams;
	wrapMechanism.ulParameterLen = 2;

	rv = C_WrapKey(hSession, &wrapMechanism, database[index].trusted_key_handle,
			database[index].encryption_key_handle, wrappedKey, &wrappedKeyLen);

	if (rv != CKR_OK) {
		printf("Wrapping not successful: %x\n", rv);
		return -1;
	}


	printf("### Export Database Entry:\n");
	printf("URL: %s\n", database[index].url);
	printf("Username: %s\n", database[index].username);
	printf("Password Encrypted: ");
	print_hex(database[index].password, 32);
	printf("IV: ");
	print_hex(ctrParams.cb, 16);
	printf("Wrapped Key: ");
	print_hex(wrappedKey, 16);


	return 0;
}




/* Importing an Entry requires to unwrap a key together with a new DB entry
 *
 */

int import_db_entry(struct pw_db database[32],
		unsigned char username[256],
		unsigned char url[256],
		unsigned char password[32],
		unsigned char iv[16],
		unsigned char wrappedKey[16]) {


	CK_SESSION_HANDLE hSession = 1;
	CK_MECHANISM mechanism;

	CK_OBJECT_CLASS keyClass = CKO_SECRET_KEY;
	CK_KEY_TYPE keyType = CKK_AES;
	CK_BBOOL true = CK_TRUE;
	CK_RV rv;

	/* Usage Key Template */
	CK_OBJECT_HANDLE hUnwrappingKey;
	CK_ATTRIBUTE usageKeyTemplate[] = {
			{CKA_CLASS, &keyClass, sizeof(keyClass)},
			{CKA_KEY_TYPE, &keyType, sizeof(keyType)},
			{CKA_ENCRYPT, &true, sizeof(true)},
			{CKA_DECRYPT, &true, sizeof(true)},
			{CKA_SENSITIVE, &true, sizeof(true)},
			{CKA_EXTRACTABLE, &true, sizeof(true)},
			{CKA_WRAP_WITH_TRUSTED, &true, sizeof(true)}
	};

	CK_AES_CTR_PARAMS ctrParams;

	memcpy(ctrParams.cb, iv, 16);

	ctrParams.ulCounterBits = 128;

	/* the handle of the unwrapped key */
	CK_OBJECT_HANDLE hSecretKey;

	mechanism.mechanism = CKM_AES_CTR;
	mechanism.pParameter = (void*) &ctrParams;
	mechanism.ulParameterLen = 2;


	rv = C_UnwrapKey(hSession, &mechanism, database[0].trusted_key_handle,
			wrappedKey, 16, usageKeyTemplate, 7, &hSecretKey);

	if (rv != CKR_OK) {
		printf("Unwrapping unsuccesful: %x\n", rv);
		return rv;
	}

	/* Now add entry to the database, if possible */
	int index = -1, i = 0;
	/* Search next free db entry */
	for ( i = 0 ; i < 32; i++) {
		if (database[i].index == -1) {
			index = 1;
			break;
		}
	}
	if (index == -1) {
		printf("You already have 32 Passwords stored!\n");
		return -1;
	}

	database[index].encryption_key_handle = hSecretKey;
	strncpy(database[index].url , url , 256);
	strncpy(database[index].username, username, 256);
	memcpy(database[index].password, password, 16);
	memcpy(database[index].iv, cb, 16);
	database[index].index = index;


	printf("\nSuccessfully added a password to the Password Manager!\n");
	return 0;
}

int get_user_input() {
	printf("\nChoose an option\n\n");
	printf("(1) Add Entry\t\t\t(2) Remove Entry\n");
	printf("(3) Show Entries\t\t(4) Get Password\n");
	printf("(5) Export Entry\t\t(6) Import Entry\n");
	printf("(9) Quit\n\n> ");
	int c;
	c = get_char();
	printf("%c\n", c);
	return c - '0';
}



void add_entry(struct pw_db database[32]) {
	char url[256];
	char username[256];
	char password[32];

	printf("\nPlease enter URL, Username and Password\n");
	printf("URL: > ");
	fgets_print(url, 256);
	printf("\nUsername: > ");
	fgets_print(username, 256);
	printf("\nPassword: > ");
	fgets(password, 32);
	printf("\n");
	encrypt_password(database, url, username, password);


}


void show_entries(struct pw_db database[32]) {
	int i;

	for (i = 0; i < 32; i ++) {
		if (database[i].index != -1) {
			printf("### Entry: %d ###\n", i);
			printf("# URL: %s\n", database[i].url);
			printf("# Username: %s\n", database[i].username);
			printf("# Password:");
			print_hex(database[i].password, 32);
			printf("\n");
		}
	}
}


void get_password(struct pw_db database[32]) {
	int index;

	printf("\nPlease enter index of Entry you want to see\n");
	printf("Index: > ");
	index = get_char();
	printf("%c\n", index);
	decrypt_password(database, index - '0');
}

void remove_entry(struct pw_db database[32]) {
	int index, res;
	printf("Please enter index of entry you want to remove\n");
	printf("Index: > ");
	index = get_char();
	printf("%c\n", index- '0');
	res = delete_entry(database, index - '0');
}

void greetings() {
	printf("#################################################\n");
	printf("##################### STH #######################\n");
	printf("############### PASSWORD MANAGER ################\n");
	printf("#################################################\n");
}





int pw_manager() {

	struct pw_db database[32];
	int i, res;
	int user_input;

	CK_RV rv;

	greetings();
	init_pw_manager(database);
	do {
		user_input = get_user_input();
			switch(user_input) {
			case ADD_ENTRY:
				add_entry(database);
				break;
			case REMOVE_ENTRY:
				remove_entry(database);
				break;
			case SHOW_ENTRIES:
				show_entries(database);
				break;
			case GET_PASSWORD:
				get_password(database);
				break;
			case EXPORT_ENTRY:
				export_db_entry(database);
				break;
			case IMPORT_ENTRY:
				printf("import entry\n");
				break;
			case QUIT:
				break;
			default:
				printf("Unknown option, try again!\n");
				break;
			}
	} while (user_input != QUIT);
	printf("Quit\n");

	rv = C_CloseSession(1);
	rv = C_Finalize(NULL);
}
